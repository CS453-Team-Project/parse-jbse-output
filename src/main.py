import argparse
import os
from typing import Tuple, Sequence

import pprint
import z3

from src.java.type import JavaType
from src.jbse.path import JBSEPath, JBSEPathAux
from src.util.arg import parse_method


curr_dir = os.getcwd()
NUM_MODELS = 10


def main(target: str, methods: Sequence[str], num_models: int, debug: bool = False):
    methods = [parse_method(method) for method in methods]

    print(methods)

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
    # print('\n\n\n$ python src/main.py -t "examples/6.txt" -m "com/cs453/group5/examples/Calculator:myFunction:(J[CI)I:number:longs:b"')
    # parser = argparse.ArgumentParser()
    # parser.add_argument("-t", "--target", required=True)
    # parser.add_argument("-m", "--method", nargs="*")
    # parser.add_argument("-n", "--nmodels")
    # parser.add_argument("-d", "--debug", action="store_true")

    # args = parser.parse_args()
    # log(*main(args.target, args.method, args.nmodels or 4, args.debug))
    # print('\n\n\n')

    with open(os.path.join(curr_dir, "examples/1/methods.txt"), "r") as f:
        methods = [r.strip() for r in f.readlines()]

    path, s, r, models = main(
        os.path.join(curr_dir, "examples/1/path2.txt"),
        methods,
        NUM_MODELS,
    )

    print("Symmap")
    pprint.pprint(path.symmap)

    print(z3.simplify(z3.And(*path.z3_clauses)))


    # assertions = s.assertions()
    # print([assertions[i] for i in range(len(assertions))])
    # print(z3.simplify(s.assertions()))
    # print(models)
