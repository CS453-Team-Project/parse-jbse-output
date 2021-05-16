from typing import Sequence
from itertools import chain, combinations

import z3


def powerset(iterable):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s) + 1))


def get_n_models(s: z3.Solver, num_models: int) -> Sequence[z3.ModelRef]:
    result = []

    while len(result) < num_models and s.check() == z3.sat:
        m = s.model()
        result.append(m)
        # Create a new constraint the blocks the current model
        block = []
        for d in m:
            # d is a declaration
            if d.arity() > 0:
                continue
            # create a constant from declaration
            c = d()
            if z3.is_array(c) or c.sort().kind() == z3.Z3_UNINTERPRETED_SORT:
                continue
            block.append(c != m[d])
        s.add(z3.Or(block))

    return result