from fnmatch import translate
import os
import argparse
from typing import Tuple, Sequence

import pprint
import z3

from src.java.type import JavaType
from src.jbse.path import JBSEPath, JBSEPathAux
from src.util.arg import parse_method

from src.util.z3_to_java import z3_to_java


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


if __name__ == "__main__":
    # Argument Parsing
    parser = argparse.ArgumentParser()
    parser.add_argument('--target','-t')
    parser.add_argument('--methods', '-m', nargs='+')

    args = parser.parse_args()
    target_path = args.target
    methods = args.methods

    # Default arguments
    if methods == None:
        with open(os.path.join(curr_dir, "examples/1/methods.txt"), "r") as f:
            methods = [r.strip() for r in f.readlines()]
    if target_path == None:
        target_path = os.path.join(curr_dir, "examples/1/path3.txt")

    # run main
    path, s, r, models = main(
        target_path,
        methods,
        NUM_MODELS,
    )

    path_condition = z3.simplify(z3.And(*path.z3_clauses))

    print("Concatenation of all clauses:")
    print(path_condition)

    # Simplification using ctx-solver-simplify tactic,
    # but it seems not that good sometimes...
    print("Simplification using ctx-solver-simplify:")
    print(z3.Tactic("ctx-solver-simplify")(path_condition))

    print("In Java syntax:")
    print(path_condition, "--->\n", z3_to_java(path_condition, path.symmap))
