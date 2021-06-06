import os
import argparse
from typing import Optional, Tuple, Sequence, Union

import pprint
import z3
from glob import glob
from src.java.type import JavaTypeArray, JavaTypeClass

from src.jbse.path import JBSEPath, JBSEPathAux, JBSEPathResultReturn
from src.jbse.path_condition import (
    PathConditionClauseAssumeNull,
)
from src.jbse.symbol import JBSESymbol, JBSESymbolRef
from src.util.arg import parse_method

from src.util.z3_to_java import (
    bv_to_java,
    z3_to_java,
    z3_to_java_without_symmap,
    z3_traverse_unparse_symbol,
)


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
                # Check null references
                def get_null_refs(path: JBSEPath) -> Sequence[str]:
                    result = [
                        (
                            next(
                                (
                                    ".".join(name for _, name in key)
                                    for key, symbol in path.symmap.items()
                                    if symbol == clause.sym_ref
                                ),
                                None,
                            )
                        )
                        for clause in path.clauses
                        if type(clause) == PathConditionClauseAssumeNull
                    ]
                    result = [item for item in result if item is not None]
                    return set(result)

                if get_null_refs(origin_path) != get_null_refs(mutant_path):
                    continue

                origin_path_result = (
                    JBSEPathResultReturn(
                        z3_traverse_unparse_symbol(
                            origin_path.result.value, origin_path.symmap
                        )
                    )
                    if type(origin_path.result) == JBSEPathResultReturn
                    else origin_path.result
                )
                mutant_path_result = (
                    JBSEPathResultReturn(
                        z3_traverse_unparse_symbol(
                            mutant_path.result.value, mutant_path.symmap
                        )
                    )
                    if type(mutant_path.result) == JBSEPathResultReturn
                    else mutant_path.result
                )

                if origin_path_result != mutant_path_result:
                    path_condition = [
                        *[
                            z3_traverse_unparse_symbol(c, origin_path.symmap)
                            for c in origin_path.z3_clauses
                        ],
                        *[
                            z3_traverse_unparse_symbol(c, mutant_path.symmap)
                            for c in mutant_path.z3_clauses
                        ],
                    ]

                    if (
                        type(mutant_path_result)
                        == type(origin_path_result)
                        == JBSEPathResultReturn
                    ):
                        path_condition.append(
                            origin_path_result.value != mutant_path_result.value
                        )

                    s = z3.Solver()
                    s.add(*path_condition)

                    if str(s.check()) == "sat":
                        # inputs = get_inputs()
                        inputs = []

                        self.kill_conditions.append(
                            {
                                "origin_pathname": origin_path.name,
                                "origin_result": origin_path.result.to_string(
                                    origin_path.symmap
                                ),
                                "mutant_pathname": mutant_path.name,
                                "mutant_result": mutant_path.result.to_string(
                                    mutant_path.symmap
                                ),
                                "path_condition": z3_to_java_without_symmap(
                                    z3.simplify(z3.And(*path_condition))
                                ),
                                "inputs": inputs,
                            }
                        )
                    elif str(s.check()) == "unknown":
                        self.unknown_conditions.append(
                            {
                                "origin_pathname": origin_path.name,
                                "origin_result": origin_path.result.to_string(
                                    origin_path.symmap
                                ),
                                "mutant_pathname": mutant_path.name,
                                "mutant_result": mutant_path.result.to_string(
                                    mutant_path.symmap
                                ),
                                "path_condition": [
                                    z3_to_java_without_symmap(cond)
                                    for cond in path_condition
                                ],
                            }
                        )


def print_parse_result(
    project: str, mutant: Optional[int], filename: str, num_models: int
):

    if mutant is None:
        target_path = os.path.join(project, "original", filename)
    else:
        target_path = os.path.join(
            project,
            "mutants",
            str(mutant),
            filename,
        )

    # run main
    path, s, r, models = main(
        target_path,
        methods,
        num_models,
    )

    path_condition = z3.simplify(z3.And(*path.z3_clauses))

    if args.verbose:
        print("Result of the path:")
        print(path.result)
        print("")

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

        print("")

    else:
        print(
            "&&".join(
                condition
                for condition in [
                    z3_to_java(path_condition, path.symmap),
                    *[
                        "("
                        + next(
                            (
                                ".".join([k[1] for k in key])
                                for (key, value) in path.symmap.items()
                                if value == clause.sym_ref
                            ),
                            None,
                        )
                        + " == null)"
                        for clause in path.clauses
                        if type(clause) == PathConditionClauseAssumeNull
                    ],
                ]
                if condition != "true"
            )
        )


# FIXME: !!!!
def get_inputs(
    models: Sequence[Tuple[z3.ModelRef, Sequence[int]]],
    z3_conditions: Sequence[z3.ExprRef],
    other_conditions: Sequence[Union[PathConditionClauseAssumeNull]],
    param_names: Sequence[str],
    symmap: dict[Sequence[Tuple[str, str]], JBSESymbol],
) -> Sequence[dict[str, str]]:
    result = []

    for i, (model, unsat_clauses) in enumerate(models):
        print("Model " + str(i) + ":")

        for param_name in param_names:
            param_dict = {}

            param_key = (("{ROOT}", param_name),)
            if param_key in symmap:
                symbol = symmap[param_key]

                # class, string, array
                if type(symbol) == JBSESymbolRef:
                    # string
                    if (
                        type(symbol.type) == JavaTypeClass
                        and symbol.type.binary_name == "java/lang/String"
                    ):
                        # null
                        if PathConditionClauseAssumeNull(symbol) in other_conditions:
                            param_dict[param_name] = "null"

                        else:
                            # get z3 result
                            raise NotImplementedError

                        raise NotImplementedError

                    # other class
                    elif type(symbol.type) == JavaTypeClass:
                        raise NotImplementedError

                    # array
                    elif type(symbol.type) == JavaTypeArray:
                        raise NotImplementedError

                # primitives
                else:
                    raise NotImplementedError


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
    parser.add_argument("--mutant", "-m", default=None, help="Mutant index (e.g. 1)")
    parser.add_argument(
        "--filename", "-f", help="Filename (e.g. path4.txt)", nargs="+", default=None
    )

    args = parser.parse_args()

    with open(os.path.join(args.project, "methods.txt"), "r") as methods_file:
        methods = [l.strip() for l in methods_file.readlines()]

    action = args.action

    if action == "parse":
        try:
            num_models = int(args.nummodels)
        except:
            num_models = NUM_MODELS

        paths_dir = (
            os.listdir(os.path.join(args.project, "mutants", str(args.mutant)))
            if args.mutant is not None
            else os.listdir(os.path.join(args.project, "original"))
        )

        for filename in args.filename or paths_dir:
            print(f"[Path: {filename}]")
            print_parse_result(args.project, args.mutant, filename, num_models)

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
