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
    Z3_OP_TRUE: "True",
    Z3_OP_FALSE: "False",
    Z3_OP_EQ: "==",
    Z3_OP_DISTINCT: "!=",
    Z3_OP_ITE: "If",
    Z3_OP_AND: "&&",
    Z3_OP_OR: "||",
    Z3_OP_IFF: "==",
    Z3_OP_XOR: "^",
    Z3_OP_NOT: "!",
    Z3_OP_IMPLIES: "Implies",
    Z3_OP_IDIV: "/",
    Z3_OP_MOD: "%",
    Z3_OP_TO_REAL: "ToReal",
    Z3_OP_TO_INT: "ToInt",
    Z3_OP_POWER: "**",
    Z3_OP_IS_INT: "IsInt",
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
    Z3_OP_BSREM: "SRem",
    Z3_OP_BUREM: "URem",
    Z3_OP_EXT_ROTATE_LEFT: "RotateLeft",
    Z3_OP_EXT_ROTATE_RIGHT: "RotateRight",
    Z3_OP_SLEQ: "<=",
    Z3_OP_SLT: "<",
    Z3_OP_SGEQ: ">=",
    Z3_OP_SGT: ">",
    Z3_OP_ULEQ: "ULE",
    Z3_OP_ULT: "ULT",
    Z3_OP_UGEQ: "UGE",
    Z3_OP_UGT: "UGT",
    Z3_OP_SIGN_EXT: "SignExt",
    Z3_OP_ZERO_EXT: "ZeroExt",
    Z3_OP_REPEAT: "RepeatBitVec",
    Z3_OP_BASHR: ">>",
    Z3_OP_BSHL: "<<",
    Z3_OP_BLSHR: "LShR",
    Z3_OP_CONCAT: "Concat",
    Z3_OP_EXTRACT: "Extract",
    Z3_OP_BV2INT: "BV2Int",
    Z3_OP_ARRAY_MAP: "Map",
    Z3_OP_SELECT: "Select",
    Z3_OP_STORE: "Store",
    Z3_OP_CONST_ARRAY: "K",
    Z3_OP_ARRAY_EXT: "Ext",
    Z3_OP_PB_AT_MOST: "AtMost",
    Z3_OP_PB_LE: "PbLe",
    Z3_OP_PB_GE: "PbGe",
    Z3_OP_PB_EQ: "PbEq",
    Z3_OP_SEQ_CONCAT: "Concat",
    Z3_OP_SEQ_PREFIX: "PrefixOf",
    Z3_OP_SEQ_SUFFIX: "SuffixOf",
    Z3_OP_SEQ_UNIT: "Unit",
    Z3_OP_SEQ_CONTAINS: "Contains",
    Z3_OP_SEQ_REPLACE: "Replace",
    Z3_OP_SEQ_AT: "At",
    Z3_OP_SEQ_NTH: "Nth",
    Z3_OP_SEQ_INDEX: "IndexOf",
    Z3_OP_SEQ_LAST_INDEX: "LastIndexOf",
    Z3_OP_SEQ_LENGTH: "Length",
    Z3_OP_STR_TO_INT: "StrToInt",
    Z3_OP_INT_TO_STR: "IntToStr",
    Z3_OP_SEQ_IN_RE: "InRe",
    Z3_OP_SEQ_TO_RE: "Re",
    Z3_OP_RE_PLUS: "Plus",
    Z3_OP_RE_STAR: "Star",
    Z3_OP_RE_OPTION: "Option",
    Z3_OP_RE_UNION: "Union",
    Z3_OP_RE_RANGE: "Range",
    Z3_OP_RE_INTERSECT: "Intersect",
    Z3_OP_RE_COMPLEMENT: "Complement",
    Z3_OP_FPA_IS_NAN: "fpIsNaN",
    Z3_OP_FPA_IS_INF: "fpIsInf",
    Z3_OP_FPA_IS_ZERO: "fpIsZero",
    Z3_OP_FPA_IS_NORMAL: "fpIsNormal",
    Z3_OP_FPA_IS_SUBNORMAL: "fpIsSubnormal",
    Z3_OP_FPA_IS_NEGATIVE: "fpIsNegative",
    Z3_OP_FPA_IS_POSITIVE: "fpIsPositive",
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
):
    symbol = JBSESymbol.parse(z3symbol.__str__())

    sym_keys = [k for k, v in symmap.items() if v == symbol][0]

    return ".".join([name for _, name in sym_keys])


def z3_to_java(t: z3.ExprRef, symmap: dict[Sequence[Tuple[str, str]], JBSESymbol]):
    if len(t.children()) == 0:

        if t.decl().kind() == z3.z3consts.Z3_OP_UNINTERPRETED:
            return unparse_symbol(t, symmap)

        else:
            return t.__str__()

    children = [z3_to_java(child, symmap) for child in t.children()]

    decl = t.decl().kind()

    try:
        opstring = z3_op_to_str[decl]
        if decl in _z3_unary:
            return f"({opstring+children[0]})"
        elif decl in _z3_infix:
            return f"({children[0] + opstring +children[1]})"
        else:
            return f"({opstring.join(children)})"
    except Exception:
        raise Exception("Operator not in z3_op_to_str.")
