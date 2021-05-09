from abc import ABC, abstractmethod
import re

from .symbol import JBSESymbolRef
from .symbol_manager import symmgr


class PathConditionClause(ABC):
    @staticmethod
    def parse(string):
        for c in [
            PathConditionClauseAssumeExpands,
            PathConditionClauseAssumeNull,
            PathConditionClauseAssume,
        ]:
            parsed = c.parse(string)
            if parsed is not None:
                return parsed

        raise ValueError("Invalid input")


class PathConditionClauseAssume(PathConditionClause):
    def __init__(self, content: str):  # TODO: parse content
        self.content = content

    @staticmethod
    def parse(string):
        return PathConditionClauseAssume(string)

    def __repr__(self) -> str:
        return self.content


# class PathConditionClauseAssumeAliases(PathConditionClause):
#     def __init__(self, heapPosition: int): # TODO: aliases
#         self.content = content


class PathConditionClauseAssumeExpands(PathConditionClause):
    def __init__(self, sym_ref: JBSESymbolRef, heap_pos: int):
        self.sym_ref = sym_ref
        self.heap_pos = heap_pos

    @staticmethod
    def parse(string):
        pattern = r"^\{R(\d+)\} == Object\[(\d+)\] \(fresh\)$"
        matched = re.search(pattern, string)
        if matched is None:
            return None
        return PathConditionClauseAssumeExpands(
            symmgr.get("R", int(matched.group(1))), int(matched.group(2))
        )

    def __repr__(self) -> str:
        return f"{repr(self.sym_ref)} == Object[{self.heap_pos}] (fresh)"


# class PathConditionClauseAssumeClassInitialized(PathConditionClause):
#     def __init__(self, content: str): #TODO
#         self.content = content


# class PathConditionClauseAssumeClassNotInitialized(PathConditionClause):
#     def __init__(self, content: str): #TODO
#         self.content = content


class PathConditionClauseAssumeNull(PathConditionClause):
    def __init__(self, sym_ref: JBSESymbolRef):
        self.sym_ref = sym_ref

    @staticmethod
    def parse(string):
        pattern = r"^\{R(\d+)\} == null$"
        matched = re.search(pattern, string)
        if matched is None:
            return None
        return PathConditionClauseAssumeExpands(symmgr.get("R", int(matched.group(1))))

    def __repr__(self) -> str:
        return f"{repr(self.sym_ref)} == null"
