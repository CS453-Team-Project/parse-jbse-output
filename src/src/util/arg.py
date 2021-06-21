from typing import Tuple

from src.java.type import JavaType


def parse_method(method: str) -> Tuple[str, str, dict, JavaType]:
    """
    Example:
        * input: "java/sdlka/Calculator:sampleMethod:(I[Z)V:num:boolArr"
        * output:
            ( 'java/sdlka/Calculator'
            , 'sampleMethod'
            , { 'num':     JavaTypeInt()
              , 'boolArr': JavaTypeArray(JavaTypeBoolean())
              }
            , JavaTypeVoid()
            )
    """

    try:
        classname, methodname, method_sig, *param_names = method.split(":")
        param_types, ret_type = JavaType.parse_method_signature(method_sig)

        assert len(param_types) == len(param_names)
    except:
        raise ValueError("Invalid input.")

    return (classname, methodname, dict(zip(param_names, param_types)), ret_type)