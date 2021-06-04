from abc import ABC, abstractmethod
import re
from typing import Optional, Literal

from src.java.type import JavaType


class JBSESymbol(ABC):
    def __eq__(self, o):
        return type(self) == type(o) and self.index == o.index

    def __hash__(self):
        return hash(repr(self))

    @staticmethod
    def parse(string: str):
        for c in [
            JBSESymbolRef,
            JBSESymbolValue,
        ]:
            parsed = c.parse(string)
            if parsed is not None:
                return parsed

        raise ValueError("Invalid input")

    def to_string_without_type(self):
        return f"{{{'R' if type(self) == JBSESymbolRef else 'V'}{self.index}}}"


class JBSESymbolRef(JBSESymbol):
    def __init__(self, index: int, sym_type: Optional[JavaType] = None):
        self.index = index
        self.type = sym_type

    def __repr__(self) -> str:
        return f"{{R{self.index}}}{'?' if self.type is None else repr(self.type)}"

    @staticmethod
    def parse(string: str):
        pattern = r"^\{R(\d+)\}$"
        matched = re.search(pattern, string)
        if matched is not None:
            return JBSESymbolRef(int(matched.group(1)))
        return None


class JBSESymbolValue(JBSESymbol):
    def __init__(self, index: int, sym_type: Optional[JavaType] = None):
        self.index = index
        self.type = sym_type

    def __repr__(self) -> str:
        return f"{{V{self.index}}}{'?' if self.type is None else repr(self.type)}"

    @staticmethod
    def parse(string: str):
        pattern = r"^\{V(\d+)\}$"
        matched = re.search(pattern, string)
        if matched is not None:
            return JBSESymbolValue(int(matched.group(1)))
        return None
