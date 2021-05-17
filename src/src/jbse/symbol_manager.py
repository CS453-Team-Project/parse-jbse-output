from typing import Literal, Optional

from src.java.type import JavaType
from .symbol import *


class JBSESymbolManager:
    def __init__(self):
        self.map: dict[Tuple[Literal["R", "V"], int], JBSESymbol] = {}

    def get(self, ref_or_value: Literal["R", "V"], index: int) -> "JBSESymbol":
        if (ref_or_value, index) in self.map:
            return self.map[(ref_or_value, index)]

        constructor = JBSESymbolRef if ref_or_value == "R" else JBSESymbolValue
        self.map[(ref_or_value, index)] = constructor(index)
        return self.map[(ref_or_value, index)]

    def get_parse(self, string: str) -> "JBSESymbol":
        if string[0] != "{" or string[-1] != "}":
            raise ValueError("Invalid input")

        string = string[1:-1]

        if string[0] in ["R", "V"]:
            try:
                return self.get(string[0], int(string[1:]))
            except ValueError:
                raise ValueError("Invalid input")

            raise ValueError("Invalid input")


symmgr = JBSESymbolManager()
