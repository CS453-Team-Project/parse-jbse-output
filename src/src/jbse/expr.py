from typing import Optional

import z3

from src.java.value import JavaValue

from .symbol_manager import JBSESymbolManager
from ..java.type import *


def eval_jbse_expr(symmgr: JBSESymbolManager, string: str):
    """
    Parse a single JBSE expression.

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
    """

    # replace WIDEN-* and NARROW-*
    # When WIDEN_or_NARROW-*({Symbol with known type}) found,
    # replace them appropriately.
    # Otherwise, just remove the conversion. TODO: possible cause of fault
    widen = {
        # WIDEN-*I
        "ZI": lambda x: f"z3.ZeroExt(31, {x})",
        "BI": lambda x: f"z3.SignExt(24, {x})",
        "SI": lambda x: f"z3.SignExt(16, {x})",
        "CI": lambda x: f"z3.ZeroExt(16, {x})",
        # WIDEN-I*
        "IJ": lambda x: f"z3.SignExt(32, {x})",
        "IF": lambda x: f"z3.ToReal(z3.BV2Int({x}, is_signed=True))",
        "ID": lambda x: f"z3.ToReal(z3.BV2Int({x}, is_signed=True))",
        # WIDEN-J*
        "JF": lambda x: f"z3.ToReal(z3.BV2Int({x}, is_signed=True))",
        "JD": lambda x: f"z3.ToReal(z3.BV2Int({x}, is_signed=True))",
        # WIDEN-F*
        "FD": lambda x: x,
    }
    narrow = {
        # NARROW-I*
        "IZ": lambda x: f"z3.If({x} == z3.BitVecVal(0, 32), z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))",
        "IB": lambda x: f"z3.Extract(7, 0, {x})",
        "IS": lambda x: f"z3.Extract(15, 0, {x})",
        "IC": lambda x: f"z3.Extract(15, 0, {x})",
        # NARROW-J*
        "JI": lambda x: f"z3.Extract(31, 0, {x})",
        # NARROW-F*
        "FI": lambda x: f"z3.Int2BV(z3.ToInt({x}), 32)",
        "FJ": lambda x: f"z3.Int2BV(z3.ToInt({x}), 64)",
        # NARROW-D*
        "DI": lambda x: f"z3.Int2BV(z3.ToInt({x}), 32)",
        "DJ": lambda x: f"z3.Int2BV(z3.ToInt({x}), 64)",
        "DF": lambda x: x,
    }

    def replace_conv(string: str) -> str:
        # "(WIDEN-ID(sth1) + WIDEN-JD(sth2))"
        #  ^
        # -> "(mywidenid(sth1) + WIDEN-JD(sth2))"
        #     - call single -    ^
        # -> "(mywidenid(sth1) + mywidenjd(sth2))"
        #                        - call single - ^
        index = 0
        pointer = 0
        while pointer < len(string):
            widen_first = string[index:].find("WIDEN-")
            narrow_first = string[index:].find("NARROW-")

            if widen_first == -1 and narrow_first == -1:
                break

            f = min(x for x in [widen_first, narrow_first] if x >= 0)
            first = index + f
            is_widening = first == index + widen_first

            pointer = first + (9 if is_widening else 10)
            index = pointer

            parentheses_depth = 1
            while True:
                if string[pointer] == "(":
                    parentheses_depth += 1
                elif string[pointer] == ")":
                    parentheses_depth -= 1

                if parentheses_depth == 0:
                    break

                pointer += 1

            replaced = replace_conv_single(
                string[first : first + (9 if is_widening else 10)]
                + string[index:pointer]
            )
            string = string[:first] + replaced + string[pointer + 1 :]

            pointer = len(replaced) + first
            index = pointer

        return string

    def replace_conv_single(string: str) -> str:
        assert string.startswith("WIDEN-") or string.startswith("NARROW-")
        is_widening = string.startswith("WIDEN-")

        index = 6 if is_widening else 7
        conversion_type = string[index : index + 2]
        conversion = (widen if is_widening else narrow)[conversion_type]

        substr_start = index + 3
        inner = replace_conv(string[substr_start:])
        return conversion(inner)

    def replace_num_lit(string: str, sign: str, digit: str, suffix: str):
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

    def replace_val_sym(string: str, index_str: str) -> str:
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
            return f"z3.Real('{{V{index}}}')"
        if symbol.type == JavaTypeDouble():
            return f"z3.Real('{{V{index}}}')"

        return string

    string = replace_conv(string)

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

    return eval(string)
