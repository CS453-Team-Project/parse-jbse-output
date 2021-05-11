from abc import ABC, abstractmethod
import re

from ..java.type import *
from .symbol import JBSESymbolRef
from .symbol_manager import symmgr

import z3


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
    def __init__(self, cond: z3.BoolRef):  # TODO: parse content
        self.cond = cond

    @staticmethod
    def parse(string):
        # XXX: Parsing the result as an AST would be the best

        # replace WIDEN-* and NARROW-*
        # When WIDENorNARROW-*({Symbol with known type}) found,
        # replace them appropriately.
        # Otherwise, just remove the conversion. TODO: possible cause of fault
        #
        # public static boolean narrows(char to, char from) {
        #     return (from == DOUBLE && (to == INT || to == LONG || to == FLOAT)) ||
        #            (from == FLOAT && (to == INT || to == LONG)) ||
        #            (from == LONG && to == INT) ||
        #            //this is for bastore, castore and sastore
        #            (from == INT && (to == BOOLEAN || to == BYTE || to == SHORT || to == CHAR));
        # }
        #
        # public static boolean widens(char to, char from) {
        #     return  (from == INT && (to == LONG || to == FLOAT || to == DOUBLE)) ||
        #             (from == LONG && (to == FLOAT || to == DOUBLE)) ||
        #             (from == FLOAT && to == DOUBLE) ||
        #             //this is for baload, caload and saload
        #             (from == BOOLEAN && to == INT) || //also for Algo_XCMPY opstack trick
        #             (from == BYTE && to == INT) ||
        #             (from == CHAR && to == INT) ||
        #             (from == SHORT && to == INT);
        # }

        def replace_conv(string, type_to_str, sym_index):
            symbol = symmgr.get("V", int(sym_index))
            type_to = JavaType.parse(type_to_str)

            if symbol.type == JavaTypeBoolean():
                if type_to == JavaTypeInt():
                    return f"z3.ZeroExt(31, ({{V{sym_index}}}))"
            elif symbol.type == JavaTypeByte():
                if type_to == JavaTypeInt():
                    return f"z3.SignExt(24, ({{V{sym_index}}}))"
            elif symbol.type == JavaTypeShort():
                if type_to == JavaTypeInt():
                    return f"z3.SignExt(16, ({{V{sym_index}}}))"
            elif symbol.type == JavaTypeChar():
                if type_to == JavaTypeInt():
                    return f"z3.ZeroExt(16, ({{V{sym_index}}}))"
            elif symbol.type == JavaTypeInt():
                if type_to == JavaTypeBoolean():
                    return f"z3.If(({{V{sym_index}}}) == z3.BitVecVal(0, 32), z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))"
                if type_to == JavaTypeByte():
                    return f"z3.Extract(7, 0, ({{V{sym_index}}}))"
                if type_to == JavaTypeShort() or type_to == JavaTypeChar():
                    return f"z3.Extract(15, 0, ({{V{sym_index}}}))"
                if type_to == JavaTypeLong():
                    return f"z3.SignExt(32, ({{V{sym_index}}}))"
                if type_to == JavaTypeFloat():
                    raise NotImplementedError("INT TO FLOAT")  # TODO:
                if type_to == JavaTypeDouble():
                    raise NotImplementedError("INT TO DOUBLE")  # TODO:
            elif symbol.type == JavaTypeLong():
                if type_to == JavaTypeInt():
                    return f"z3.Extract(31, 0, ({{V{sym_index}}}))"
                if type_to == JavaTypeFloat():
                    raise NotImplementedError("LONG TO FLOAT")  # TODO:
                if type_to == JavaTypeDouble():
                    raise NotImplementedError("LONG TO DOUBLE")  # TODO:
            elif symbol.type == JavaTypeFloat():
                if type_to == JavaTypeInt():
                    raise NotImplementedError("FLOAT TO INT")  # TODO:
                if type_to == JavaTypeLong():
                    raise NotImplementedError("FLOAT TO LONG")  # TODO:
                if type_to == JavaTypeDouble():
                    raise NotImplementedError("FLOAT TO DOUBLE")  # TODO:
            elif symbol.type == JavaTypeDouble():
                if type_to == JavaTypeInt():
                    raise NotImplementedError("FLOAT TO INT")  # TODO:
                if type_to == JavaTypeLong():
                    raise NotImplementedError("FLOAT TO LONG")  # TODO:
                if type_to == JavaTypeFloat():
                    raise NotImplementedError("FLOAT TO FLOAT")
            return string

        def replace_num_lit(string, sign, digit, suffix):
            if suffix == "" or suffix == "L":
                # integer
                num = int(digit) * (-1 if sign == "-" else 1)
                return f"z3.BitVecVal({num}, {32 if suffix == '' else 64})"

            if suffix in "fd":
                try:
                    num = float(digit) * (-1 if sign == "-" else 1)
                    return f"z3.FPVal({num}, {'FloatSingle()' if suffix == 'f' else 'FloatDouble()'})"

                except:
                    return string

            return string

        def replace_val_sym(string, index_str):
            index = int(index_str)
            symbol = symmgr.get("V", index)

            if symbol.type == JavaTypeBoolean():
                return f"z3.BitVec('{{V{index}}}', 1)"
            if symbol.type == JavaTypeByte():
                return f"z3.BitVec('{{V{index}}}', 8)"
            if symbol.type == JavaTypeShort() or symbol.type == JavaTypeChar():
                return f"z3.BitVec('{{V{index}}}', 16)"
            if symbol.type == JavaTypeInt():
                return f"z3.BitVec('{{V{index}}}', 32)"
            if symbol.type == JavaTypeLong():
                return f"z3.BitVec('{{V{index}}}', 64)"
            if symbol.type == JavaTypeFloat():
                return f"z3.FP('{{V{index}}}', z3.FloatSingle())"
            if symbol.type == JavaTypeDouble():
                return f"z3.FP('{{V{index}}}', z3.FloatDouble())"

            return string

        # widen/narrow
        # References cannot be widen or narrowed
        conv_pattern = r"((WIDEN|NARROW)\-(Z|B|C|D|F|S|I|J)\(\{V(\d+)\}\))"
        string = re.sub(
            conv_pattern, lambda match: replace_conv(*match.group(1, 3, 4)), string
        )
        # remove remaining (unknown) WIDEN/NARROW
        string = re.sub(r"(WIDEN|NARROW)\-(Z|B|C|D|F|S|I|J)", "", string)

        # number literals
        num_lit_pattern = r"(\(([+-]?)([\d\.]*)([dfL]?)\))"
        string = re.sub(
            num_lit_pattern, lambda match: replace_num_lit(*match.groups()), string
        )

        # value symbols
        val_sym_pattern = r"(\{V(\d+)\})"
        string = re.sub(
            val_sym_pattern, lambda match: replace_val_sym(*match.groups()), string
        )

        return PathConditionClauseAssume(eval(string))

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
