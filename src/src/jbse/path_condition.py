from abc import ABC
from dataclasses import dataclass
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


@dataclass
class PathConditionClauseAssume(PathConditionClause):
    cond: z3.BoolRef

    @staticmethod
    def parse(symmgr: JBSESymbolManager, string: str):
        return PathConditionClauseAssume(eval_jbse_expr(symmgr, string))

    def __repr__(self) -> str:
        return repr(self.cond)


# class PathConditionClauseAssumeAliases(PathConditionClause):
#     def __init__(self, heapPosition: int): # TODO: aliases
#         self.content = content


@dataclass
class PathConditionClauseAssumeExpands(PathConditionClause):
    sym_ref: JBSESymbolRef
    heap_pos: int

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


@dataclass
class PathConditionClauseAssumeNull(PathConditionClause):
    sym_ref: JBSESymbolRef

    @staticmethod
    def parse(symmgr: JBSESymbolManager, string: str):
        pattern = r"^\{R(\d+)\} == null$"
        matched = re.search(pattern, string)
        if matched is None:
            return None
        return PathConditionClauseAssumeNull(symmgr.get("R", int(matched.group(1))))

    def __repr__(self) -> str:
        return f"{repr(self.sym_ref)} == null"
