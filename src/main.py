from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Tuple, Optional, Any, Union
import re

import pprint
import z3

from src.java.type import *
from src.jbse.symbol import *
from src.jbse.path_condition import *
from src.jbse.heap import *
from src.jbse.symbol_manager import symmgr


@dataclass
class JBSEPath:
    name: str
    ret_val: Optional[str]  # TODO: parse ret val
    symmap: dict[str, JBSESymbol]  # TODO: parse value type of symmap
    clauses: list[PathConditionClause]
    heap: dict[int, JBSEHeapValue]
    # static_store: TODO
    # stack: TODO

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
    def parse(string: str):
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
            return (key, symmgr.get_parse(value_str))

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
        if matched is None:
            raise ValueError("Improper input")
        stack_str = matched.group(1)

        for match in re.finditer(r"(Frame\[\d+\]: \{(.|\r|\n)*?\n\t\})", stack_str):
            # TODO: more information required to extract?
            frame_str = match.group(1)
            for var_match in re.finditer(r"Variable\[(\d+)\]: Name: (.*?), Type: (.*?), Value: (.*?)\s*(\(type: .*\))?\s*\n", frame_str):
                sym_match = re.search(r"\{(R|V)(\d+)\}", var_match.group(4))
                if sym_match is not None:
                    ref_or_value = sym_match.group(1)
                    index = int(sym_match.group(2))
                    symbol = symmgr.get(ref_or_value, index)
                    symbol.type = JavaType.parse(var_match.group(3))

        # TODO: static store

        return JBSEPath(pathname, ret_val, symmap, clauses, heap)

    def solve(self):
        # assumption: .parse was called beforehand

        z3Vars = {}

        for clause in self.clauses:
            if type(clause) != PathConditionClauseAssume:
                continue

            # TODO!!!!!!!!
            # TODO!!!!!!!!
            # TODO!!!!!!!!
            # TODO!!!!!!!!
            # TODO!!!!!!!!
            # TODO!!!!!!!!
            # TODO!!!!!!!!
            # TODO!!!!!!!!


            clause = '({V6}) >= (-128)'

            

            pass

        def java_type_to_z3(java_type: JavaType):
            if java_type == JavaTypeBoolean():
                return z3.Bool
            if java_type == JavaTypeByte():
                return z3.
            # BitVecVal(-1, 16)
            if java_type == JavaTypeChar():
                return lambda x: z3.BitVec(x, 8)
            if java_type == JavaTypeDouble():
                return lambda x: z3.FP(x, z3.FloatDouble())
            if java_type == JavaTypeFloat():
                return lambda x: z3.FP(x, z3.FloatSingle())
            if java_type == JavaTypeInt():
                return z3.Int # z3.Int
            if java_type == JavaTypeLong():
                return z3.Int # 

            raise ValueError("Invalid Java type generating a Z3 variable")
            
        assume_clauses = [
            eval(re.sub("(\{V\d+\})", "z3Vars['\\1']", clause))
            for clause in self.clauses
            if type(clause) == PathConditionClauseAssume
        ]
        z3.solve(*parsed_clauses)



        pass
        
if __name__ == "__main__":
    # with open("examples/2.txt", "r") as f:
    #     pprint.pprint \
    #     (JBSEPath.parse("".join(f.readlines())), \
    #     indent=4, compact=False
    #     )

    symbols = [
        ("V0", JavaTypeInt()),
        ("V2", JavaTypeInt()),
        ("V5", JavaTypeInt()),
        ("V6", JavaTypeInt()),
        ("V7", JavaTypeInt())
    ]
    # z3VarV2 = Int('{V2}')
    z3Vars = {}
    for (name, type_desc) in symbols:
        z3Vars[name] = Int(f"{{{name}}}")

    clauses = [
        "({V0}) < (4)",
        "(0) < ({V0})",
        "({V2}) >= (0)",
        "(0) < ({V2})",
        "({V5}) >= (-128)",
        "({V5}) <= (127)",
        "({V5}) + (128) == (0)",
        "(1) < ({V0})",
        "(1) < ({V2})",
        "({V6}) >= (-128)",
        "({V6}) <= (127)",
        "({V6}) + (128) == (0)",
        "(2) < ({V0})",
        "(2) < ({V2})",
        "({V7}) >= (-128)",
        "({V7}) <= (127)",
        "({V7}) + (128) == (132)"
    ]
    parsed_clauses = [
        eval(re.sub("\{(V\d+)\}", "z3Vars['\\1']", clause)) for clause in clauses
    ]

    
    solve(*parsed_clauses)
