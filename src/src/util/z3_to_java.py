from z3 import *
from typing import Tuple, Sequence

from src.java.type import *
from src.jbse.symbol import *


##########################################################################################
#
# Constants
#
# ########################################################################################


########################################################################################
#
# Dict that converts z3 operators to java syntax string
#
# Dictionary is not perfect, so if something is not converted well, you might have to modify this.
#
# ****There are no unsigned numbers in java, so I intentionally didn't do Unsigned ops ******
#
# This is modified from z3printer._z3_op_to_str
##########################################################################################

z3_op_to_str = {
    # Z3_OP_TRUE: "True",
    # Z3_OP_FALSE: "False",
    Z3_OP_EQ: "==",
    Z3_OP_DISTINCT: "!=",
    Z3_OP_AND: "&&",
    Z3_OP_OR: "||",
    Z3_OP_IFF: "==",
    Z3_OP_XOR: "^",
    Z3_OP_NOT: "!",
    Z3_OP_ADD: "+",
    Z3_OP_SUB: "-",
    Z3_OP_MUL: "*",
    Z3_OP_IDIV: "/",
    Z3_OP_MOD: "%",
    Z3_OP_POWER: "**",
    Z3_OP_LE: "<=",
    Z3_OP_LT: "<",
    Z3_OP_GE: ">=",
    Z3_OP_GT: ">",
    Z3_OP_BADD: "+",
    Z3_OP_BSUB: "-",
    Z3_OP_BMUL: "*",
    Z3_OP_BOR: "|",
    Z3_OP_BAND: "&",
    Z3_OP_BNOT: "~",
    Z3_OP_BXOR: "^",
    Z3_OP_BNEG: "-",
    Z3_OP_BUDIV: "/",
    Z3_OP_BSDIV: "/",
    Z3_OP_BSMOD: "%",
    Z3_OP_SLEQ: "<=",
    Z3_OP_SLT: "<",
    Z3_OP_SGEQ: ">=",
    Z3_OP_SGT: ">",
    Z3_OP_BASHR: ">>",
    Z3_OP_BSHL: "<<",
}

_z3_unary = [Z3_OP_UMINUS, Z3_OP_BNOT, Z3_OP_BNEG, Z3_OP_NOT]
_z3_infix = [
    Z3_OP_EQ,
    Z3_OP_IFF,
    Z3_OP_ADD,
    Z3_OP_SUB,
    Z3_OP_MUL,
    Z3_OP_DIV,
    Z3_OP_IDIV,
    Z3_OP_MOD,
    Z3_OP_POWER,
    Z3_OP_LE,
    Z3_OP_LT,
    Z3_OP_GE,
    Z3_OP_GT,
    Z3_OP_BADD,
    Z3_OP_BSUB,
    Z3_OP_BMUL,
    Z3_OP_BSDIV,
    Z3_OP_BSMOD,
    Z3_OP_BOR,
    Z3_OP_BAND,
    Z3_OP_BXOR,
    Z3_OP_BSDIV,
    Z3_OP_SLEQ,
    Z3_OP_SLT,
    Z3_OP_SGEQ,
    Z3_OP_SGT,
    Z3_OP_BASHR,
    Z3_OP_BSHL,
]

####################################################################################################################################
#
# Constants End
#
####################################################################################################################################


def unparse_symbol(
    z3symbol: z3.ExprRef, symmap: dict[Sequence[Tuple[str, str]], JBSESymbol]
) -> str:
    symbol = JBSESymbol.parse(z3symbol.__str__())

    sym_keys = [k for k, v in symmap.items() if v == symbol][0]

    return ".".join([name for _, name in sym_keys])


def bv_to_java(t: z3.BitVecNumRef):
    size = t.params()[1]

    if size == 1:
        return "false" if t.params()[0] == "0" else "true"

    if size == 8:
        val = int(t.params()[0])
        return f"(byte) {val if val < 128 else val - 256}"

    if size == 16:
        return f"(char) {t.params()[0]}"

    if size == 32:
        val = int(t.params()[0])
        return str(val if val < 2 ** 31 else val - 2 ** 32)

    if size == 64:
        val = int(t.params()[0])
        return f"{val if val < 2 ** 63 else val - 2 ** 64}L"

    return str(t)


def z3_to_java(
    t: z3.ExprRef, symmap: dict[Sequence[Tuple[str, str]], JBSESymbol]
) -> str:
    if str(t) in ["True", "False"]:
        return str(t).lower()

    decl = t.decl().kind()

    if len(t.children()) == 0:
        if decl == Z3_OP_UNINTERPRETED:
            return unparse_symbol(t, symmap)

        if type(t) == z3.RatNumRef:
            num_literal = t.as_decimal(prec=17).replace("?", "")

            if "." not in num_literal:
                return f"{num_literal}.0d"

            return f"{num_literal}d"

        if decl == Z3_OP_BNUM:
            return bv_to_java(t)

        else:
            return str(t)

    if decl in _z3_unary:
        return f"({z3_op_to_str[decl] + z3_to_java(t.children()[0], symmap)})"

    if decl in _z3_infix:
        return f"({z3_to_java(t.children()[0], symmap) + z3_op_to_str[decl] + z3_to_java(t.children()[1], symmap)})"

    # BI, SI, IJ
    if decl == Z3_OP_SIGN_EXT:
        if len(t.params()) == 1 and len(t.children()) == 1:
            offset = t.params()[0]
            child = t.children()[0]

            if offset == 24 or offset == 16:  # {Byte, Short} -> Int
                return f"(int)({z3_to_java(child, symmap)})"

            if offset == 32:  # Int -> Long
                return f"(long)({z3_to_java(child, symmap)})"

            raise ValueError("invalid offset")

    # ZI, CI
    if decl == Z3_OP_ZERO_EXT:
        if len(t.children()) == 1:
            child = t.children()[0]

            return f"(int)({z3_to_java(child, symmap)})"

    # * -> D (assuming F does not appear in the source code)
    if decl == Z3_OP_TO_REAL:
        if len(t.children()) == 1:
            child = t.children()[0]
            if child.decl().kind() == Z3_OP_ITE:
                cond, true_branch, false_branch = child.children()
                if type(cond) == z3.BoolRef and cond.decl().kind() != Z3_OP_EQ:
                    grandchild = (
                        true_branch
                        if len(str(true_branch)) < len(str(false_branch))
                        else false_branch
                    ).children()[0]
                    return f"(double)({z3_to_java(grandchild, symmap)})"

            if child.decl().kind() == Z3_OP_BV2INT:
                return f"(double)({z3_to_java(child.chlidren()[0], symmap)})"

            return f"(double)({z3_to_java(child, symmap)})"

    # IZ
    if decl == Z3_OP_ITE:
        if len(t.children()) == 3:
            cond, true_branch, false_branch = t.children()
            if (
                type(cond) == z3.BoolRef
                and cond.decl().kind() == Z3_OP_EQ
                and type(true_branch) == z3.BitVecNumRef
                and true_branch.params() == ["0", 1]
                and type(false_branch) == z3.BitVecNumRef
                and false_branch.params() == ["1", 1]
            ):
                zero_num_ref = cond.children()[0]
                if (
                    type(zero_num_ref) == z3.BitVecNumRef
                    and zero_num_ref.params()[0] == "0"
                ):
                    return f"(bool)({z3_to_java(cond.children()[1], symmap)})"

    # IB, IC, JI, assuming short does not appear in the source code
    if decl == Z3_OP_EXTRACT:
        if len(t.children()) == 1 and len(t.params()) == 2:
            child = t.children()[0]
            upper_bound, lower_bound = t.params()

            if lower_bound == 0:
                if upper_bound == 7:
                    return f"(byte)({z3_to_java(child, symmap)})"

                if upper_bound == 15:
                    return f"(char)({z3_to_java(child, symmap)})"

                if upper_bound == 31:
                    return f"(int)({z3_to_java(child, symmap)})"

    # D -> int-like (assuming F does not appear in the source code)
    if decl == Z3_OP_INT2BV:
        if (
            len(t.children()) == 1
            and t.children()[0].decl().kind() == z3.Z3_OP_TO_INT
            and len(t.params()) == 1
        ):
            child = t.children()[0].children()[0]
            offset = t.params()[0]

            if offset == 32:
                return f"(int)({z3_to_java(child, symmap)})"

            if offset == 64:
                return f"(long)({z3_to_java(child, symmap)})"

            raise ValueError("invalid offset")

    if decl in z3_op_to_str:
        children = [z3_to_java(child, symmap) for child in t.children()]
        return f"({z3_op_to_str[decl].join(children)})"

    raise ValueError("invalid expression: " + str(t))


def z3_traverse_unparse_symbol(
    t: z3.ExprRef, symmap: dict[Sequence[Tuple[str, str]], JBSESymbol]
) -> z3.ExprRef:
    def get_single_substitution(key: Sequence[Tuple[str, str]], symbol: JBSESymbol):
        new_name = ".".join(name for _, name in key)
        return (jbse_symbol_to_z3(symbol), jbse_symbol_to_z3(symbol, new_name))

    substitutions = [
        get_single_substitution(key, symbol)
        for key, symbol in symmap.items()
        if type(symbol) == JBSESymbolValue
    ]

    return z3.substitute(t, substitutions)


def z3_to_java_without_symmap(t: z3.ExprRef):
    if str(t) in ["True", "False"]:
        return str(t).lower()

    decl = t.decl().kind()

    if len(t.children()) == 0:
        if decl == Z3_OP_UNINTERPRETED:
            return str(t)

        if type(t) == z3.RatNumRef:
            num_literal = t.as_decimal(prec=17).replace("?", "")

            if "." not in num_literal:
                return f"{num_literal}.0d"

            return f"{num_literal}d"

        if decl == Z3_OP_BNUM:
            return bv_to_java(t)

        else:
            return str(t)

    if decl in _z3_unary:
        return f"({z3_op_to_str[decl] + z3_to_java_without_symmap(t.children()[0])})"

    if decl in _z3_infix:
        return f"({z3_to_java_without_symmap(t.children()[0]) + z3_op_to_str[decl] + z3_to_java_without_symmap(t.children()[1])})"

    # BI, SI, IJ
    if decl == Z3_OP_SIGN_EXT:
        if len(t.params()) == 1 and len(t.children()) == 1:
            offset = t.params()[0]
            child = t.children()[0]

            if offset == 24 or offset == 16:  # {Byte, Short} -> Int
                return f"(int)({z3_to_java_without_symmap(child)})"

            if offset == 32:  # Int -> Long
                return f"(long)({z3_to_java_without_symmap(child)})"

            raise ValueError("invalid offset")

    # ZI, CI
    if decl == Z3_OP_ZERO_EXT:
        if len(t.children()) == 1:
            child = t.children()[0]

            return f"(int)({z3_to_java_without_symmap(child)})"

    # * -> D (assuming F does not appear in the source code)
    if decl == Z3_OP_TO_REAL:
        if len(t.children()) == 1:
            child = t.children()[0]
            if child.decl().kind() == Z3_OP_ITE:
                cond, true_branch, false_branch = child.children()
                if type(cond) == z3.BoolRef and cond.decl().kind() != Z3_OP_EQ:
                    grandchild = (
                        true_branch
                        if len(str(true_branch)) < len(str(false_branch))
                        else false_branch
                    ).children()[0]
                    return f"(double)({z3_to_java_without_symmap(grandchild)})"

            if child.decl().kind() == Z3_OP_BV2INT:
                return f"(double)({z3_to_java_without_symmap(child.chlidren()[0])})"

            return f"(double)({z3_to_java_without_symmap(child)})"

    # IZ
    if decl == Z3_OP_ITE:
        if len(t.children()) == 3:
            cond, true_branch, false_branch = t.children()
            if (
                type(cond) == z3.BoolRef
                and cond.decl().kind() == Z3_OP_EQ
                and type(true_branch) == z3.BitVecNumRef
                and true_branch.params() == ["0", 1]
                and type(false_branch) == z3.BitVecNumRef
                and false_branch.params() == ["1", 1]
            ):
                zero_num_ref = cond.children()[0]
                if (
                    type(zero_num_ref) == z3.BitVecNumRef
                    and zero_num_ref.params()[0] == "0"
                ):
                    return f"(bool)({z3_to_java_without_symmap(cond.children()[1])})"

    # IB, IC, JI, assuming short does not appear in the source code
    if decl == Z3_OP_EXTRACT:
        if len(t.children()) == 1 and len(t.params()) == 2:
            child = t.children()[0]
            upper_bound, lower_bound = t.params()

            if lower_bound == 0:
                if upper_bound == 7:
                    return f"(byte)({z3_to_java_without_symmap(child)})"

                if upper_bound == 15:
                    return f"(char)({z3_to_java_without_symmap(child)})"

                if upper_bound == 31:
                    return f"(int)({z3_to_java_without_symmap(child)})"

    # D -> int-like (assuming F does not appear in the source code)
    if decl == Z3_OP_INT2BV:
        if (
            len(t.children()) == 1
            and t.children()[0].decl().kind() == z3.Z3_OP_TO_INT
            and len(t.params()) == 1
        ):
            child = t.children()[0].children()[0]
            offset = t.params()[0]

            if offset == 32:
                return f"(int)({z3_to_java_without_symmap(child)})"

            if offset == 64:
                return f"(long)({z3_to_java_without_symmap(child)})"

            raise ValueError("invalid offset")

    if decl in z3_op_to_str:
        children = [z3_to_java_without_symmap(child) for child in t.children()]
        return f"({z3_op_to_str[decl].join(children)})"

    raise ValueError("invalid expression: " + str(t))


def jbse_symbol_to_z3(symbol: JBSESymbol, name_: Optional[str] = None) -> str:
    def wrapper():
        index = symbol.index
        name = name_ or f"{{V{index}}}"

        if symbol.type == JavaTypeBoolean():
            return f"z3.BitVec('{name}', 1)"
        if symbol.type == JavaTypeByte():
            return f"z3.BitVec('{name}', 8)"
        if symbol.type == JavaTypeShort() or symbol.type == JavaTypeChar():
            return f"z3.BitVec('{name}', 16)"
        if symbol.type == JavaTypeInt():
            return f"z3.BitVec('{name}', 32)"
        if symbol.type == JavaTypeLong():
            return f"z3.BitVec('{name}', 64)"
        if symbol.type == JavaTypeFloat():
            return f"z3.Real('{name}')"
        if symbol.type == JavaTypeDouble():
            return f"z3.Real('{name}')"

        raise ValueError(f"Invalid type of the symbol {symbol}")

    return eval(wrapper())
