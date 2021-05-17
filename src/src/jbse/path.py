from dataclasses import dataclass
from itertools import chain, combinations
from typing import Tuple, Optional, Any, Union, Sequence
import re

import z3

from src.java.type import *
from src.jbse.symbol import *
from src.jbse.path_condition import *
from src.jbse.heap import *
from src.jbse.symbol_manager import symmgr
from src.util.math import *


@dataclass
class JBSEPathAux:
    """Auxiliary data for JBSEPath."""

    methods: Sequence[Tuple[str, str, dict, JavaType]]


@dataclass
class JBSEPath:
    name: str
    ret_val: Optional[str]  # TODO: parse ret val
    symmap: dict[
        Sequence[Tuple[str, str]], JBSESymbol
    ]  # TODO: parse value type of symmap
    clauses: list[PathConditionClause]
    heap: dict[int, JBSEHeapValue]
    # static_store: TODO

    def __repr__(self):
        symmap_str = ""
        for key in self.symmap:
            symmap_str += f"        {key}: {self.symmap[key]}\n"
        symmap_str = f"{{\n{symmap_str}    }}"

        clauses_str = ",\n        ".join([repr(c) for c in self.clauses])

        heap_str = ""
        for key in self.heap:
            heap_str += f"        {key}: {repr(self.heap[key])}\n"
        heap_str = f"{{\n{heap_str}    }}"

        return (
            "JBSEPATH(\n"
            f"    name={repr(self.name)}\n"
            f"    ret_val={repr(self.ret_val)}\n"
            f"    symmap={symmap_str}\n"
            f"    clauses=[\n        {clauses_str}\n    ]\n"
            f"    heap={heap_str}\n"
            ")"
        )

    @staticmethod
    def parse(string: str, aux: JBSEPathAux):
        # pathname
        pathname_pattern = r"((\.\d+)+\[\d+\])\s*\r?\nLeaf state"
        matched = re.search(pathname_pattern, string)
        if matched is None:
            raise ValueError("Improper input")
        pathname = matched.group(1)

        # returned value
        ret_val_pattern = r"\nLeaf state, returned value: (.*?)\r?\n"
        matched = re.search(ret_val_pattern, string)
        ret_val = None if matched is None else matched.group(1)

        # symbol map
        symmap_pattern = r"where:\s*\r?\n((.|\r|\n)*?)\r?\nStatic store:"
        matched = re.search(symmap_pattern, string)
        if matched is None:
            raise ValueError("Improper input")
        symmap_str = matched.group(1)

        def parse_symmap_entry(
            entry: str,
        ) -> Tuple[Sequence[Tuple[Optional[str], str]], JBSESymbol]:
            value_str, key = entry.split(" == ")
            symbol = symmgr.get_parse(value_str)

            # set parameter types
            # e.g., key = "{ROOT}:s.java/lang/String:value.length"

            # parameters = [('{ROOT}', 's'), ('java/lang/String', 'value'), (None, 'length')]
            parameters = tuple(
                [
                    (a[0], a[1]) if len(a) >= 2 else (None, a[0])
                    for a in [s.split(":") for s in key.split(".")]
                ]
            )

            return (parameters, symbol)

        symmap = dict(
            [parse_symmap_entry(entry.strip()) for entry in symmap_str.split("&&")]
        )

        for binary_name, method_name, param_types, ret_type in aux.methods:
            for param_name, param_type in param_types.items():
                if (("{ROOT}", param_name),) in symmap:
                    symmap[(("{ROOT}", param_name),)].type = param_type

        # heap
        heap_pattern = r"Heap:\s*\{\s*\r?\n*((.|\r|\n)*?)\n\}"
        matched = re.search(heap_pattern, string)
        if matched is None:
            raise ValueError("Improper input")
        heap_str = matched.group(1)

        heap = {}
        for match in re.finditer(r"(Object\[(\d+)\]: \{(.|\r|\n)*?\n\t\})", heap_str):
            heap[match.group(2)] = JBSEHeapValue.parse(match.group(1), symmap)

        # stack
        stack_pattern = r"Stack:\s*\{\s*\r?\n*((.|\r|\n)*?)\n\}"
        matched = re.search(stack_pattern, string)
        # it is possible to not have stack frame showing
        if matched is not None:
            stack_str = matched.group(1)

            for match in re.finditer(r"(Frame\[\d+\]: \{(.|\r|\n)*?\n\t\})", stack_str):
                # TODO: more information required to extract?
                frame_str = match.group(1)
                for var_match in re.finditer(
                    r"Variable\[(\d+)\]: Name: (.*?), Type: (.*?), Value: (.*?)\s*(\(type: .*\))?\s*\n",
                    frame_str,
                ):
                    sym_match = re.search(r"\{(R|V)(\d+)\}", var_match.group(4))
                    if sym_match is not None:
                        ref_or_value = sym_match.group(1)
                        index = int(sym_match.group(2))
                        symbol = symmgr.get(ref_or_value, index)
                        symbol.type = JavaType.parse(var_match.group(3))

        # TODO: static store

        # path condition
        pathcond_pattern = r"Path condition:\s*\r?\n((.|\r|\n)*?)\r?\n\t*where:"
        matched = re.search(pathcond_pattern, string)
        if matched is None:
            raise ValueError("Improper input")
        pathcond_str = matched.group(1)

        clauses = [
            PathConditionClause.parse(entry.strip())
            for entry in pathcond_str.split("&&")
        ]

        return JBSEPath(pathname, ret_val, symmap, clauses, heap)

    @property
    def z3_clauses(self):
        return [c.cond for c in self.clauses if type(c) == PathConditionClauseAssume]

    def solve(
        self, num_models: int
    ) -> Tuple[
        z3.Solver,
        z3.CheckSatResult,  # sat, unknown, unsat
        Sequence[Tuple[z3.ModelRef, Sequence[int]]],  # [(<model>, <unsat clauses>)]
    ]:
        # TODO: which clauses should be put into the z3 solver?
        clauses = self.z3_clauses

        s = z3.Solver()
        s.add(*clauses)

        if s.check() == z3.unsat:
            return (s, z3.unsat, [])

        if s.check() == z3.unknown:
            return self.try_solve_unknown(clauses, num_models)

        models = get_n_models(s, num_models)
        return (s, z3.sat, list(zip(models, [[]] * len(models))))

    def try_solve_unknown(
        self, clauses: Sequence[z3.BoolRef], num_models: int
    ) -> Tuple[
        z3.Solver,
        z3.CheckSatResult,  # sat, unknown, unsat
        Sequence[Tuple[z3.ModelRef, Sequence[int]]],  # [(<model>, <unsat clauses>)]
    ]:
        # try reduce
        print(
            "There are some clauses that the Z3 cannot solve."
            "Try reducing path conditions..."
        )

        result = []
        s = z3.Solver()

        for excluded_indices in powerset(range(len(clauses))):
            if len(excluded_indices) == 0 or len(excluded_indices) == len(clauses):
                continue

            s.reset()
            s.add(
                *[clauses[i] for i in range(len(clauses)) if i not in excluded_indices]
            )

            if s.check() == z3.unsat:
                # XXX: impossible
                return (s, z3.unsat, [])

            if s.check() == z3.unknown:
                continue

            models = get_n_models(s, num_models - len(result))
            result.extend(zip(models, [excluded_indices] * len(models)))

            if len(result) >= num_models:
                return (s, z3.unknown, result)

        return (s, z3.unknown, result)