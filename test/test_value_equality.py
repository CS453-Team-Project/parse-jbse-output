import sys
import pytest
import os

import z3
from src.jbse.heap import JBSEHeapClassField, JBSEHeapValueClass

curr_dir = os.getcwd()
sys.path.insert(1, os.path.join(curr_dir, "src"))

from src.util.z3_to_java import z3_to_java
from src.jbse.path import JBSEPathResultReturn, JBSEPathResultException
from src.jbse.symbol import *
from src.java.type import *
from src.java.value import *


def test_JavaValueSymbolic():
    a = JavaValueSymbolic(JBSESymbol.parse("{R4}"))
    b = JavaValueSymbolic(JBSESymbol.parse("{R4}"))
    assert a == b


def test_JavaValueSimple():
    a = JavaValueSimple("D", 3)
    b = JavaValueSimple("D", 3)
    assert a == b


def test_JavaValueFromHeap():
    a = JavaValueFromHeap(3032)
    b = JavaValueFromHeap(3032)
    assert a == b


def test_JavaValueSubscript():
    a = JavaValueSubscript(JavaValueFromHeap(1018), JavaValueSimple("I", 2))
    b = JavaValueSubscript(JavaValueFromHeap(1018), JavaValueSimple("I", 2))
    assert a == b


def test_JavaValueSubscriptUnderscore():
    a = JavaValueSubscriptUnderscore(JavaValueFromHeap(4328), "_ + 0")
    b = JavaValueSubscriptUnderscore(JavaValueFromHeap(4328), "_ + 0")
    assert a == b


def test_JavaValueUnknown():
    a = JavaValueUnknown("$jaskdj%")
    b = JavaValueUnknown("$jaskdj%")
    assert a == b


def test_JBSEPathResultReturn():
    a = JBSEPathResultReturn(JavaValueSimple("I", 0))
    b = JBSEPathResultReturn(JavaValueSimple("I", 0))
    assert a == b


def test_JBSEPathResultException():
    a = JBSEPathResultException(
        JBSEHeapValueClass(
            4327,
            None,
            (0, "java/lang/NullPointerException"),
            [
                JBSEHeapClassField(
                    "detailedMessage",
                    "Ljava/lang/String;",
                    JavaValueSimple("Ljava/lang/String;", None),
                ),
                JBSEHeapClassField(
                    "cause",
                    "Ljava/lang/Throwable;",
                    JavaValueSimple("Ljava/lang/Throwable;", None),
                ),
                JBSEHeapClassField(
                    "backtrace", "Ljava/lang/Object;", JavaValueFromHeap(4328)
                ),
                JBSEHeapClassField(
                    "stackTrace",
                    "Ljava/lang/StackTraceElement;",
                    JavaValueSimple("[Ljava/lang/StackTraceElement;", None),
                ),
                JBSEHeapClassField(
                    "suppressedExceptions",
                    "Ljava/util/List;",
                    JavaValueSimple("Ljava/util/List;", None),
                ),
            ],
        )
    )
    b = JBSEPathResultException(
        JBSEHeapValueClass(
            4327,
            None,
            (0, "java/lang/NullPointerException"),
            [
                JBSEHeapClassField(
                    "detailedMessage",
                    "Ljava/lang/String;",
                    JavaValueSimple("Ljava/lang/String;", None),
                ),
                JBSEHeapClassField(
                    "cause",
                    "Ljava/lang/Throwable;",
                    JavaValueSimple("Ljava/lang/Throwable;", None),
                ),
                JBSEHeapClassField(
                    "backtrace", "Ljava/lang/Object;", JavaValueFromHeap(4328)
                ),
                JBSEHeapClassField(
                    "stackTrace",
                    "Ljava/lang/StackTraceElement;",
                    JavaValueSimple("[Ljava/lang/StackTraceElement;", None),
                ),
                JBSEHeapClassField(
                    "suppressedExceptions",
                    "Ljava/util/List;",
                    JavaValueSimple("Ljava/util/List;", None),
                ),
            ],
        )
    )
    assert a == b
