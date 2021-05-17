import sys
import pytest
import os

import z3

curr_dir = os.getcwd()
sys.path.insert(1, os.path.join(curr_dir, "src"))

from src.util.z3_to_java import z3_to_java
from src.jbse.symbol import *
from src.java.type import *

NUM_MODELS = 10

symmap = {
    (("{ROOT}", "mybool"),): JBSESymbolValue(0, JavaTypeBoolean()),
    (("{ROOT}", "mybyte"),): JBSESymbolValue(1, JavaTypeByte()),
    (("{ROOT}", "mychar"),): JBSESymbolValue(2, JavaTypeChar()),
    (("{ROOT}", "myshort"),): JBSESymbolValue(3, JavaTypeShort()),
    (("{ROOT}", "myint"),): JBSESymbolValue(4, JavaTypeInt()),
    (("{ROOT}", "mylong"),): JBSESymbolValue(5, JavaTypeLong()),
    (("{ROOT}", "myfloat"),): JBSESymbolValue(6, JavaTypeFloat()),
    (("{ROOT}", "mydouble"),): JBSESymbolValue(7, JavaTypeDouble()),
}


def test_single_var():
    result = z3_to_java(z3.And(z3.Bool("{V0}")), symmap)
    assert result == "(mybool)"


def test_conjunctive():
    result = z3_to_java(
        (
            z3.ToReal(
                z3.BV2Int(
                    (z3.Int2BV(z3.ToInt(z3.RealVal(0.3) + (z3.Real("{V6}"))), 32))
                    + z3.BitVecVal(3, 32),
                    is_signed=True,
                )
            )
        )
        + (
            z3.ToReal(
                z3.BV2Int(
                    (z3.Int2BV(z3.ToInt(z3.RealVal(0.3) + (z3.Real("{V6}"))), 32))
                    + (z3.ZeroExt(16, z3.BitVec("{V2}", 16)))
                    + z3.BitVecVal(40, 32),
                    is_signed=True,
                )
            )
        )
        >= z3.RealVal(0.0),
        symmap,
    )
    print(result)
    assert False
