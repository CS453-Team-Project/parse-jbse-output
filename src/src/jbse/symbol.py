from abc import ABC, abstractmethod
import re


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


class JBSESymbolRef(JBSESymbol):
    def __init__(self, index: int):
        self.index = index

    def __repr__(self) -> str:
        return f"{{R{self.index}}}"

    @staticmethod
    def parse(string: str):
        pattern = r"^\{R(\d+)\}$"
        matched = re.search(pattern, string)
        if matched is not None:
            return JBSESymbolRef(int(matched.group(1)))
        return None


class JBSESymbolValue(JBSESymbol):
    def __init__(self, index: int):
        self.index = index

    def __repr__(self) -> str:
        return f"{{V{self.index}}}"

    @staticmethod
    def parse(string: str):
        pattern = r"^\{V(\d+)\}$"
        matched = re.search(pattern, string)
        if matched is not None:
            return JBSESymbolValue(int(matched.group(1)))
        return None