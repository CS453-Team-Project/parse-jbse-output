from abc import ABC
import re

from ..java.type import *
from .expr import eval_jbse_expr
from .symbol import JBSESymbolRef
from .symbol_manager import JBSESymbolManager

import z3


class PathConditionClause(ABC):
    @staticmethod
    def parse(symmgr: JBSESymbolManager, string: str):
        for c in [
            PathConditionClauseAssumeExpands,
            PathConditionClauseAssumeNull,
            PathConditionClauseAssume,
        ]:
            parsed = c.parse(symmgr, string)
            if parsed is not None:
                return parsed

        raise ValueError("Invalid input")


class PathConditionClauseAssume(PathConditionClause):
    def __init__(self, cond: z3.BoolRef):
        self.cond = cond

    @staticmethod
    def parse(symmgr: JBSESymbolManager, string: str):
        return PathConditionClauseAssume(eval_jbse_expr(symmgr, string))

    def __repr__(self) -> str:
        return repr(self.cond)


# class PathConditionClauseAssumeAliases(PathConditionClause):
#     def __init__(self, heapPosition: int): # TODO: aliases
#         self.content = content


class PathConditionClauseAssumeExpands(PathConditionClause):
    def __init__(self, sym_ref: JBSESymbolRef, heap_pos: int):
        self.sym_ref = sym_ref
        self.heap_pos = heap_pos

    @staticmethod
    def parse(symmgr: JBSESymbolManager, string: str):
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
#     def __init__(self, content: str): # TODO: class initialized
#         self.content = content


# class PathConditionClauseAssumeClassNotInitialized(PathConditionClause):
#     def __init__(self, content: str): # TODO: class not initialized
#         self.content = content


class PathConditionClauseAssumeNull(PathConditionClause):
    def __init__(self, sym_ref: JBSESymbolRef):
        self.sym_ref = sym_ref

    @staticmethod
    def parse(symmgr: JBSESymbolManager, string: str):
        pattern = r"^\{R(\d+)\} == null$"
        matched = re.search(pattern, string)
        if matched is None:
            return None
        return PathConditionClauseAssumeNull(symmgr.get("R", int(matched.group(1))))

    def __repr__(self) -> str:
        return f"{repr(self.sym_ref)} == null"
