from z3 import *
from typing import Tuple, Sequence

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
        return 'false' if t.params()[0] == '0' else 'true'

    if size == 8:
        val = int(t.params()[0])
        return f'(byte){val if val < 128 else val - 256}'

    if size == 16:
        return f'(char){t.params()[0]}'

    if size == 32:
        val = int(t.params()[0])
        return str(val if val < 2 ** 31 else val - 2 ** 32)

    if size == 64:
        val = int(t.params()[0])
        return f'{val if val < 2 ** 63 else val - 2 ** 64}L'

    return str(t)


def z3_to_java(
    t: z3.ExprRef, symmap: dict[Sequence[Tuple[str, str]], JBSESymbol]
) -> str:
    # print("        ====================================================")
    # print("        expr: ", t, "expr type", type(t), "expr params", t.params())

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
            print("decl kind", cond.decl().kind())
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