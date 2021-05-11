import argparse
from dataclasses import dataclass
from itertools import chain, combinations
from typing import Tuple, Optional, Any, Union, Sequence
import re

import pprint
import z3

from src.java.type import *
from src.jbse.symbol import *
from src.jbse.path_condition import *
from src.jbse.heap import *
from src.jbse.symbol_manager import symmgr


@dataclass
class JBSEPathAux:
    """Auxiliary data for JBSEPath."""

    methods: Sequence[Tuple[str, str, dict, JavaType]]


@dataclass
class JBSEPath:
    name: str
    ret_val: Optional[str]  # TODO: parse ret val
    symmap: dict[str, JBSESymbol]  # TODO: parse value type of symmap
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

        def parse_symmap_entry(entry: str) -> Tuple[JBSESymbol, str]:
            value_str, key = entry.split(" == ")
            symbol = symmgr.get_parse(value_str)

            # set parameter types
            if key.startswith("{ROOT}:"):
                if re.match(r"^[A-Za-z0-9$_]*$", key[len("{ROOT}:") :]):
                    field = key[len("{ROOT}:") :]
                    if field == "this":
                        symbol.type = JavaTypeClass(aux.methods[0][0])
                    elif field in aux.methods[0][2]:
                        symbol.type = aux.methods[0][2][field]

            return (key, symbol)

        symmap = dict(
            [parse_symmap_entry(entry.strip()) for entry in symmap_str.split("&&")]
        )

        # heap
        heap_pattern = r"Heap:\s*\{\s*\r?\n*((.|\r|\n)*?)\n\}"
        matched = re.search(heap_pattern, string)
        if matched is None:
            raise ValueError("Improper input")
        heap_str = matched.group(1)

        heap = {}
        for match in re.finditer(r"(Object\[(\d+)\]: \{(.|\r|\n)*?\n\t\})", heap_str):
            heap[match.group(2)] = JBSEHeapValue.parse(match.group(1))

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
        self, num_models: int = 1
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
        self, clauses: Sequence[z3.BoolRef], num_models: int = 1
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


# example
# input: "java/sdlka/Calculator:sampleMethod:(I[Z)V:num:boolArr"
# output: ('java/sdlka/Calculator', 'sampleMethod', {'num': I, 'boolArr': [Z}, V)
def parse_method(method: str) -> list[Tuple[str, str, dict, JavaType]]:
    try:
        classname, methodname, method_sig, *param_names = method.split(":")
        param_types, ret_type = JavaType.parse_method_signature(method_sig)

        assert len(param_types) == len(param_names)
    except:
        raise ValueError("Invalid input.")

    return (classname, methodname, dict(zip(param_names, param_types)), ret_type)


def powerset(iterable):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s) + 1))


def get_n_models(s: z3.Solver, num_models: int = 1) -> Sequence[z3.ModelRef]:
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


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("-t", "--target", required=True)
    parser.add_argument("-m", "--method", nargs="*")
    parser.add_argument("-d", "--debug", action="store_true")

    args = parser.parse_args()
    methods = [parse_method(method) for method in args.method]

    with open(args.target, "r") as f:
        content = "".join(f.readlines())

    path = JBSEPath.parse(content, JBSEPathAux(methods))
    if args.debug:
        pprint.pprint(
            path,
            indent=4,
            compact=False,
        )

    s, r, models = path.solve(num_models=4)
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
            print(f"The path {path.name} is partially satisfiable with the following model(s).")
            for i, (m, u) in enumerate(models):
                print(f"{i + 1}.", repr(m))
                print("    Unsatisfied clauses: ", [path.z3_clauses[i] for i in u])
    else:
        print(f"The path {path.name} is satisfiable with the following model(s).")
        for i, (m, _) in enumerate(models):
            print(f"{i + 1}.", repr(m))

    #
    # where
    # ...
    # {V1} == Object[51321]:param

    # Object[51321] -> type (class) -> access param type...

    # symbols = [
    #     ("V0", JavaTypeInt()),
    #     ("V2", JavaTypeInt()),
    #     ("V5", JavaTypeInt()),
    #     ("V6", JavaTypeInt()),
    #     ("V7", JavaTypeInt())
    # ]
    # # z3VarV2 = Int('{V2}')
    # z3Vars = {}
    # for (name, type_desc) in symbols:
    #     z3Vars[name] = z3.Int(f"{{{name}}}")

    # clauses = [
    #     "({V0}) < (4)",
    #     "(0) < ({V0})",
    #     "({V2}) >= (0)",
    #     "(0) < ({V2})",
    #     "({V5}) >= (-128)",
    #     "({V5}) <= (127)",
    #     "({V5}) + (128) == (0)",
    #     "(1) < ({V0})",
    #     "(1) < ({V2})",
    #     "({V6}) >= (-128)",
    #     "({V6}) <= (127)",
    #     "({V6}) + (128) == (0)",
    #     "(2) < ({V0})",
    #     "(2) < ({V2})",
    #     "({V7}) >= (-128)",
    #     "({V7}) <= (127)",
    #     "({V7}) + (128) == (132)"
    # ]
    # parsed_clauses = [
    #     eval(re.sub("\{(V\d+)\}", "z3Vars['\\1']", clause)) for clause in clauses
    # ]

    # z3.solve(*parsed_clauses)
