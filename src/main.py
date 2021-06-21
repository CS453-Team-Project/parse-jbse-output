import os
import argparse
import re
from typing import Optional, Tuple, Sequence

import pprint
import z3
from glob import glob
from src.jbse.junit import inputs_to_junits
from src.jbse.kill import KillConditionFinder

from src.jbse.path import JBSEPath, JBSEPathAux
from src.jbse.path_condition import (
    PathConditionClauseAssumeNull,
)
from src.util.arg import parse_method

from src.util.z3_to_java import (
    bv_to_java,
    z3_to_java,
)


curr_dir = os.getcwd()
NUM_MODELS = 4


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


def print_parse_result(
    project: str,
    mutant: Optional[int],
    filename: str,
    num_models: int,
    verbose: bool = False,
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

    if verbose:
        print("Result of the path:")
        print(path.result)
        print("")

        print("Concatenation of all clauses:")
        print(path_condition)
        print("")

        # Simplification using ctx-solver-simplify tactic,
        # but it seems not that good at times...
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

            for clause in path.null_clauses:
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
        stringified_condition = "&&".join(
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

        if stringified_condition == "":
            stringified_condition = "true"

        print(stringified_condition)


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

    try:
        num_models = int(args.nummodels)
    except:
        num_models = NUM_MODELS

    if action == "parse":
        paths_dir = (
            os.listdir(os.path.join(args.project, "mutants", str(args.mutant)))
            if args.mutant is not None
            else os.listdir(os.path.join(args.project, "original"))
        )

        for filename in args.filename or paths_dir:
            print(f"[Path: {filename}]")
            print_parse_result(
                args.project, args.mutant, filename, num_models, args.verbose
            )

    if action == "kill":
        origin, mutant = glob(f"{args.project}/original/*.txt"), glob(
            f"{args.project}/mutants/{args.mutant}/*.txt"
        )

        origin = ["".join(open(file).readlines()) for file in origin]
        mutant = ["".join(open(file).readlines()) for file in mutant]

        finder = KillConditionFinder(origin, mutant, methods, num_models)
        finder.find_kill()

        if args.verbose:
            pprint.pprint(finder.kill_conditions)
            pprint.pprint(finder.unknown_conditions)

        print(
            "\n\n".join(
                [
                    inputs_to_junits(
                        i,
                        c["origin_pathname"],
                        c["origin_result_string"],
                        c["origin_result_description"],
                        args.mutant,
                        c["mutant_pathname"],
                        c["mutant_result_description"],
                        c["inputs"],
                        finder.methods,
                    )
                    for i, c in enumerate(finder.kill_conditions)
                ]
            )
        )
