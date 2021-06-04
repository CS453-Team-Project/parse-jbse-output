from fnmatch import translate
import os
import argparse
from typing import Tuple, Sequence

import pprint
import z3
from glob import glob

from src.java.type import JavaType
from src.java.value import JavaValueFromHeap, JavaValueSimple, JavaValueSymbolic
from src.jbse.path import JBSEPath, JBSEPathAux, JBSEPathResultReturn
from src.jbse.path_condition import (
    PathConditionClauseAssume,
    PathConditionClauseAssumeNull,
)
from src.jbse.symbol import JBSESymbol, JBSESymbolRef
from src.util.arg import parse_method

from src.util.z3_to_java import bv_to_java, z3_to_java


curr_dir = os.getcwd()
NUM_MODELS = 10


def main(target: str, methods: Sequence[str], num_models: int, debug: bool = False):
    methods = [parse_method(method) for method in methods]

    with open(target, "r") as f:
        content = "".join(f.readlines())

    path = JBSEPath.parse(content, JBSEPathAux(methods))
    if debug:
        pprint.pprint(
            path,
            indent=4,
            compact=False,
        )

    s, r, models = path.solve(num_models)

    return path, s, r, models


def log(
    path: JBSEPath,
    s: z3.Solver,
    r: z3.CheckSatResult,
    models: Sequence[Tuple[z3.ModelRef, Sequence[int]]],
):
    print("============================================================")
    for key, value in path.symmap.items():
        print(repr(value)[:4], "====>", key)

    if r == z3.unsat:
        # XXX: probably this is already filtered out from JBSE results.
        print(f"The path {path.name} is unreachable.")
    elif r == z3.unknown:
        if models == []:
            print(
                "The Z3 did not solve any clauses!"
                "So we have no information for this path."
            )
        else:
            print(
                f"The path {path.name} is partially satisfiable with the following model{'' if len(models) == 1 else 's'}."
            )
            for i, (m, u) in enumerate(models):
                print(f"{i + 1}.", repr(m))
                print("    Unsatisfied clauses: ", [path.z3_clauses[i] for i in u])
    else:
        print(
            f"The path {path.name} is satisfiable with the following model{'' if len(models) == 1 else 's'}."
        )
        for i, (m, _) in enumerate(models):
            print(f"{i + 1}.", repr(m))


class KillConditionFinder:
    def __init__(
        self,
        origin_paths: Sequence[str],
        mutant_paths: Sequence[str],
        methods: Sequence[str],
    ):
        methods = [parse_method(method) for method in methods]

        self.origin_paths: list[JBSEPath] = [
            JBSEPath.parse(target_path, JBSEPathAux(methods))
            for target_path in origin_paths
        ]
        self.mutant_paths: list[JBSEPath] = [
            JBSEPath.parse(target_path, JBSEPathAux(methods))
            for target_path in mutant_paths
        ]
        self.kill_conditions = list()
        self.unknown_conditions = list()

    def find_kill(self):
        for mutant_path in self.mutant_paths:
            for origin_path in self.origin_paths:
                # TODO: what if both are symbolic?
                if mutant_path.result != origin_path.result:
                    path_condition = [*origin_path.z3_clauses, *mutant_path.z3_clauses]

                    # TODO: strengthen mutant_path.result != origin_path.result
                    # TODO: support more cases
                    if (
                        type(mutant_path.result)
                        == type(origin_path.result)
                        == JBSEPathResultReturn
                    ):
                        if (
                            type(mutant_path.result.value) == JavaValueSymbolic
                            and type(origin_path.result.value) == JavaValueSimple
                        ):
                            symbol: JBSESymbol = mutant_path.result.value.symbol
                            clause = PathConditionClauseAssume.parse(
                                mutant_path.symmgr,
                                f"({{{'R' if type(symbol) == JBSESymbolRef else 'V'}{symbol.index}}}) != ({origin_path.result.value.unparse()})",
                            )
                            if clause is not None:
                                path_condition.append(clause.cond)

                        if (
                            type(origin_path.result.value) == JavaValueSymbolic
                            and type(mutant_path.result.value) == JavaValueSimple
                        ):
                            symbol: JBSESymbol = origin_path.result.value.symbol
                            clause = PathConditionClauseAssume.parse(
                                origin_path.symmgr,
                                f"({{{'R' if type(symbol) == JBSESymbolRef else 'V'}{symbol.index}}}) != ({mutant_path.result.value.unparse()})",
                            )
                            if clause is not None:
                                path_condition.append(clause.cond)

                        # TODO: what if both are symbolic

                    s = z3.Solver()
                    s.add(*path_condition)

                    if str(s.check()) == "sat":
                        self.kill_conditions.append(
                            {
                                "origin_pathname": origin_path.name,
                                "origin_result": origin_path.result,
                                "mutant_pathname": mutant_path.name,
                                "mutant_result": mutant_path.result,
                                "path_condition": path_condition,
                            }
                        )
                    elif str(s.check()) == "unknown":
                        self.unknown_conditions.append(
                            {
                                "origin_pathname": origin_path.name,
                                "origin_result": origin_path.result,
                                "mutant_pathname": mutant_path.name,
                                "mutant_result": mutant_path.result,
                                "path_condition": path_condition,
                            }
                        )


if __name__ == "__main__":
    # Argument Parsing
    parser = argparse.ArgumentParser()
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose mode")
    parser.add_argument(
        "--nummodels", "-n", default=NUM_MODELS, help="# of models (e.g. 10)"
    )
    parser.add_argument("--action", "-a", choices=["parse", "kill"], default="kill")
    parser.add_argument(
        "--project",
        "-p",
        required=True,
        help="Project directory path (e.g. examples/1)",
    )
    parser.add_argument("--mutant", "-m", nargs="+", default=[], help="Mutant indices (e.g. 0 2 3)")
    parser.add_argument("--filename", "-f", help="Filename (e.g. path4.txt)")

    args = parser.parse_args()

    with open(os.path.join(args.project, "methods.txt"), "r") as methods_file:
        methods = [l.strip() for l in methods_file.readlines()]

    action = args.action

    if action == "parse":
        try:
            num_models = int(args.nummodels)
        except:
            num_models = NUM_MODELS

        if len(args.mutant) > 1:
            parser.error(
                "There should be at most one mutant specified to run in `parse` action."
            )

        if args.mutant == []:
            target_path = os.path.join(
                args.project, "original", args.filename or "path1.txt"
            )
        else:
            target_path = os.path.join(
                args.project,
                "mutants",
                str(args.mutant[0]),
                args.filename or "path1.txt",
            )

        # run main
        path, s, r, models = main(
            target_path,
            methods,
            num_models,
        )

        path_condition = z3.simplify(z3.And(*path.z3_clauses))

        if args.verbose:
            print("Concatenation of all clauses:")
            print(path_condition)
            print("")

            # Simplification using ctx-solver-simplify tactic,
            # but it seems not that good sometimes...
            print("Simplification using ctx-solver-simplify:")
            print(z3.Tactic("ctx-solver-simplify")(path_condition))
            print("")

            print("Path condition in Java syntax:")
            print(path_condition, "--->")
            print("    " + z3_to_java(path_condition, path.symmap))
            print("")

            print("Models:")
            for i, (model, unsat_clauses) in enumerate(models):
                print("Model " + str(i) + ":")

                if len(unsat_clauses) != 0:
                    print("   ", "Unsatisfied clauses:")
                    for j, clause in enumerate(unsat_clauses):
                        print("   ", "   ", str(j) + ".", clause)

                print("   ", "Assignments:")

                stringified_conditions = []

                for variable in model:
                    name = variable.name()
                    variable = variable()
                    stringified_conditions.append(
                        next(
                            (
                                ".".join([k[1] for k in key])
                                for key, value in path.symmap.items()
                                if value == path.symmgr.get_parse(name)
                            ),
                            None,
                        )
                        + " = "
                        + bv_to_java(model.evaluate(variable))
                    )

                for clause in path.clauses:
                    if type(clause) == PathConditionClauseAssumeNull:
                        stringified_conditions.append(
                            next(
                                (
                                    ".".join([k[1] for k in key])
                                    for (key, value) in path.symmap.items()
                                    if value == clause.sym_ref
                                ),
                                None,
                            )
                            + " == null",
                        )

                print(
                    ";\n".join("        " + x for x in stringified_conditions),
                    end=";\n",
                )

        else:
            # print(z3_to_java(path_condition, path.symmap))

            for model, unsat_clauses in models:
                stringified_conditions = []

                for variable in model:
                    name = variable.name()
                    variable = variable()
                    stringified_conditions.append(
                        next(
                            (
                                ".".join([k[1] for k in key])
                                for key, value in path.symmap.items()
                                if value == path.symmgr.get_parse(name)
                            ),
                            None,
                        )
                        + " = "
                        + bv_to_java(model.evaluate(variable))
                    )

                for clause in path.clauses:
                    if type(clause) == PathConditionClauseAssumeNull:
                        stringified_conditions.append(
                            next(
                                (
                                    ".".join([k[1] for k in key])
                                    for (key, value) in path.symmap.items()
                                    if value == clause.sym_ref
                                ),
                                None,
                            )
                            + " == null",
                        )

                print(" && ".join(stringified_conditions) + ";")

    if action == "kill":
        origin, mutant = glob(f"{args.project}/original/*.txt"), glob(
            f"{args.project}/mutants/{args.mutant}/*.txt"
        )

        origin = ["".join(open(file).readlines()) for file in origin]
        mutant = ["".join(open(file).readlines()) for file in mutant]

        finder = KillConditionFinder(origin, mutant, methods)

        finder.find_kill()

        pprint.pprint(finder.kill_conditions)
        pprint.pprint(finder.unknown_conditions)
