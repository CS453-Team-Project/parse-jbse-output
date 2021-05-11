import argparse
from dataclasses import dataclass
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
                if re.match("^[A-Za-z0-9$_]*$", key[len("{ROOT}:") :]):
                    field = key[len("{ROOT}:") :]
                    if field == "this":
                        symbol.type = JavaTypeClass(aux.methods[0][0])
                    elif field in aux.methods[0][2]:
                        symbol.type = aux.methods[0][2][field]

            return (key, symbol)

        symmap = dict(
            [parse_symmap_entry(entry.strip()) for entry in symmap_str.split("&&")]
        )

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

        # frame ->
        # * method name
        # * local vars: {R*} / {V*} -> type

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

        return JBSEPath(pathname, ret_val, symmap, clauses, heap)

    # def solve(self):
    #     # assumption: .parse was called beforehand

    # preprocess clausses before expression parser
    # WIDEN, NARROW

    # int
    # boo - zero extension

    # parse clauses using python expression parser

    # use z3 to solve

    #     z3Vars = {}

    #     for clause in self.clauses:
    #         if type(clause) != PathConditionClauseAssume:
    #             continue

    #         # TODO!!!!!!!!
    #         # TODO!!!!!!!!
    #         # TODO!!!!!!!!
    #         # TODO!!!!!!!!
    #         # TODO!!!!!!!!
    #         # TODO!!!!!!!!
    #         # TODO!!!!!!!!
    #         # TODO!!!!!!!!

    #         clause = '({V6}) >= (-128)'

    #         pass

    #     def java_type_to_z3(java_type: JavaType):
    #         if java_type == JavaTypeBoolean():
    #             return z3.Bool
    #         if java_type == JavaTypeByte():
    #             return z3.
    #         # BitVecVal(-1, 16)
    #         if java_type == JavaTypeChar():
    #             return lambda x: z3.BitVec(x, 8)
    #         if java_type == JavaTypeDouble():
    #             return lambda x: z3.FP(x, z3.FloatDouble())
    #         if java_type == JavaTypeFloat():
    #             return lambda x: z3.FP(x, z3.FloatSingle())
    #         if java_type == JavaTypeInt():
    #             return z3.Int # z3.Int
    #         if java_type == JavaTypeLong():
    #             return z3.Int #

    #         raise ValueError("Invalid Java type generating a Z3 variable")

    #     assume_clauses = [
    #         eval(re.sub("(\{V\d+\})", "z3Vars['\\1']", clause))
    #         for clause in self.clauses
    #         if type(clause) == PathConditionClauseAssume
    #     ]
    #     z3.solve(*parsed_clauses)

    #     pass


# example
# input: "java/sdlka/Calculator:sampleMethod:(I[Z)V:num:boolArr"
# output: ('java/sdlka/Calculator', 'sampleMethod', {'num': I, 'boolArr': [Z}, V)
def parse_method(method: str) -> list:
    split = method.split(":")

    try:
        classname, methodname, method_sig = split[:3]
        param_names = split[3:]

        param_types, ret_type = JavaType.parse_method_signature(method_sig)

        assert len(param_types) == len(param_names)
    except:
        raise ValueError("invalid input")

    return (classname, methodname, dict(zip(param_names, param_types)), ret_type)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("-t", "--target", required=True)
    parser.add_argument("-m", "--method", nargs="*")

    args = parser.parse_args()

    target = args.target

    methods = [parse_method(method) for method in args.method]
    print(methods)

    with open("examples/4.txt", "r") as f:
        pprint.pprint(
            JBSEPath.parse("".join(f.readlines()), JBSEPathAux(methods)),
            indent=4,
            compact=False,
        )

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
