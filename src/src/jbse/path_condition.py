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
        """
        Parse a single path condition of type Assume.

        XXX: Parsing the result as an AST would be the best

        The flow of parsing is as follows:
            1. Resolve type conversions: WIDEN-* and NARROW-*
            2. Translate numeric literals
            3. Replace symbols by Z3 variables

        For type conversions, see the following code from the source code of JBSE.

        ```java
        public static boolean narrows(char to, char from) {
            return (from == DOUBLE && (to == INT || to == LONG || to == FLOAT)) ||
                   (from == FLOAT && (to == INT || to == LONG)) ||
                   (from == LONG && to == INT) ||
                   //this is for bastore, castore and sastore
                   (from == INT && (to == BOOLEAN || to == BYTE || to == SHORT || to == CHAR));
        }

        public static boolean widens(char to, char from) {
            return  (from == INT && (to == LONG || to == FLOAT || to == DOUBLE)) ||
                    (from == LONG && (to == FLOAT || to == DOUBLE)) ||
                    (from == FLOAT && to == DOUBLE) ||
                    //this is for baload, caload and saload
                    (from == BOOLEAN && to == INT) || //also for Algo_XCMPY opstack trick
                    (from == BYTE && to == INT) ||
                    (from == CHAR && to == INT) ||
                    (from == SHORT && to == INT);
        }
        ```

        XXX:

        TODO: the following is not implemented
        The first step is required to resolve nested type conversions, such as:
        ```java
        char b;
        double f = (double)((int)b);
        ```
        which is transformed by JBSE into `(WIDEN-D(WIDEN-I({V1})))`.
        (`1` here is arbitrary.) By adding type descriptor in front of this,
        the conversion process is as follows: (whitespaces are added to
        increase legibility)
        ```
        (WIDEN-D (WIDEN-I ({V1})))
        ----add type desc---->  (WIDEN-D (WIDEN-I <C>({V1})))
        ---replace WIDEN-I--->  (WIDEN-D
                                    <I>(z3.ZeroExt (16, ({V1}))))
        ---replace WIDEN-D--->  <R>(z3.ToReal                     # R for real
                                    (z3.BV2Int(
                                        (z3.ZeroExt (16, ({V1}))
                                       , is_signed=True))
        ```
        """

        # replace WIDEN-* and NARROW-*
        # When WIDEN_or_NARROW-*(<type>{Symbol with known type}) found,
        # replace them appropriately.
        # Otherwise, just remove the conversion. TODO: possible cause of fault
        def replace_conv(string, type_from_str, type_to_str):
            type_from = JavaType.parse(type_from_str)
            type_to = JavaType.parse(type_to_str)

            if type_from == JavaTypeBoolean():
                if type_to == JavaTypeInt():
                    return f"z3.ZeroExt(31, ({{V{sym_index}}}))"

            elif type_from == JavaTypeByte():
                if type_to == JavaTypeInt():
                    return f"z3.SignExt(24, ({{V{sym_index}}}))"

            elif type_from == JavaTypeShort():
                if type_to == JavaTypeInt():
                    return f"z3.SignExt(16, ({{V{sym_index}}}))"

            elif type_from == JavaTypeChar():
                if type_to == JavaTypeInt():
                    return f"z3.ZeroExt(16, ({{V{sym_index}}}))"

            elif type_from == JavaTypeInt():
                if type_to == JavaTypeBoolean():
                    return f"z3.If(({{V{sym_index}}}) == z3.BitVecVal(0, 32), z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))"
                if type_to == JavaTypeByte():
                    return f"z3.Extract(7, 0, ({{V{sym_index}}}))"
                if type_to == JavaTypeShort() or type_to == JavaTypeChar():
                    return f"z3.Extract(15, 0, ({{V{sym_index}}}))"
                if type_to == JavaTypeLong():
                    return f"z3.SignExt(32, ({{V{sym_index}}}))"
                if type_to == JavaTypeFloat() or type_to == JavaTypeDouble():
                    return f"z3.ToReal(z3.BV2Int(({{V{sym_index}}}), is_signed=True))"
            elif type_from == JavaTypeLong():
                if type_to == JavaTypeInt():
                    return f"z3.Extract(31, 0, ({{V{sym_index}}}))"
                if type_to == JavaTypeFloat() or type_to == JavaTypeDouble():
                    return f"z3.ToReal(z3.BV2Int(({{V{sym_index}}}), is_signed=True))"
            elif type_from == JavaTypeFloat():
                if type_to == JavaTypeInt():
                    return f"z3.ToReal(z3.(({{V{sym_index}}})))"
                if type_to == JavaTypeLong():
                    raise NotImplementedError("FLOAT TO LONG")  # TODO:
                if type_to == JavaTypeDouble():
                    raise NotImplementedError("FLOAT TO DOUBLE")  # TODO:
            elif type_from == JavaTypeDouble():
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
                    return f"z3.RealVal({num})"

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
        widen = {
            # WIDEN-*I
            "ZI": lambda x: z3.ZeroExt(31, x),
            "BI": lambda x: z3.SignExt(24, x),
            "SI": lambda x: z3.SignExt(16, x),
            "CI": lambda x: z3.ZeroExt(16, x),
            # WIDEN-I*
            "IJ": lambda x: z3.SignExt(32, x),
            "IF": lambda x: z3.ToReal(z3.BV2Int(x, is_signed=True)),
            "ID": lambda x: z3.ToReal(z3.BV2Int(x, is_signed=True)),
            # WIDEN-J*
            "JF": lambda x: z3.ToReal(z3.BV2Int(x, is_signed=True)),
            "JD": lambda x: z3.ToReal(z3.BV2Int(x, is_signed=True)),
            # WIDEN-F*
            "FD": lambda x: x,
        }
        narrow = {
            # NARROW-I*
            "IZ": lambda x: z3.If(
                x == z3.BitVecVal(0, 32), z3.BitVecVal(1, 1), z3.BitVecVal(0, 1)
            ),
            "IB": lambda x: z3.Extract(7, 0, x),
            "IS": lambda x: z3.Extract(15, 0, x),
            "IC": lambda x: z3.Extract(15, 0, x),
            # NARROW-J*
            "JI": lambda x: z3.Extract(31, 0, x),
            # NARROW-F*
            "FI": lambda x: z3.Int2BV(z3.ToInt(x), 32),
            "FJ": lambda x: z3.Int2BV(z3.ToInt(x), 64),
            # NARROW-D*
            "DI": lambda x: z3.Int2BV(z3.ToInt(x), 32),
            "DJ": lambda x: z3.Int2BV(z3.ToInt(x), 64),
            "DF": lambda x: x,
        }
        string = re.sub(
            r"(WIDEN|NARROW)\-(Z|B|C|D|F|S|I|J)(Z|B|C|D|F|S|I|J)",
            lambda match: rf"{match.group(1).lower()}['{match.group(2)}{match.group(3)}']",
            string,
        )

        # number literals
        num_lit_pattern = r"(\(([+-]?)(\d[\d\.]*)([dfL]?)\))"
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
        return PathConditionClauseAssumeNull(symmgr.get("R", int(matched.group(1))))

    def __repr__(self) -> str:
        return f"{repr(self.sym_ref)} == null"
