from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Tuple, Optional, Any, Union
import re

import pprint

from src.java.type import *
from src.jbse.symbol import *
from src.jbse.path_condition import *
from src.jbse.heap import *


@dataclass
class JBSEPath:
    name: str
    ret_val: Optional[str]  # TODO: parse ret val
    symmap: dict[JBSESymbol, str]  # TODO: parse value type of symmap
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
            key_str, value = entry.split(" == ")
            return (JBSESymbol.parse(key_str), value)

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
        for match in re.finditer(r"(Object\[(\d+)\]: \{(.|\r|\n)*?\n\t\})", string):
            heap[match.group(2)] = JBSEHeapValue.parse(match.group(1))

        # TODO: static store & stack

        return JBSEPath(pathname, ret_val, symmap, clauses, heap)


if __name__ == "__main__":
    with open("examples/2.txt", "r") as f:
        pprint.pprint(JBSEPath.parse("".join(f.readlines())), indent=4, compact=False)
