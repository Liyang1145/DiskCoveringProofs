"""Lossless data-only encoding for an experimental original arithmetic context.

No source ownership or geometric proof is supplied by this codec.
"""

from fractions import Fraction as F
from math import isfinite


def integer(text):
    if type(text) is not str:
        raise ValueError("typed context integer must use a canonical decimal string")
    result = int(text)
    if str(result) != text:
        raise ValueError("typed context integer is not canonical")
    return result


def pack(value):
    kind = type(value)
    if value is None:
        return ["null"]
    if kind is bool:
        return ["bool", value]
    if kind is int:
        return ["int", str(value)]
    if kind is str:
        return ["str", value]
    if isinstance(value, F):
        return ["fraction", str(value.numerator), str(value.denominator)]
    if kind is float:
        if not isfinite(value):
            raise ValueError("nonfinite floating metadata is not a typed arithmetic context")
        return ["binary-float", value.hex()]
    if kind is list:
        return ["list", [pack(item) for item in value]]
    if kind is tuple:
        return ["tuple", [pack(item) for item in value]]
    if kind is dict:
        if any(type(key) is not str for key in value):
            raise ValueError("typed context dictionaries require string keys")
        return ["dict", [[key, pack(item)] for key, item in value.items()]]
    raise ValueError("opaque arithmetic context value cannot be serialized: " + kind.__name__)


def unpack(node):
    if type(node) is not list or not node or type(node[0]) is not str:
        raise ValueError("typed arithmetic context has an invalid tag")
    tag = node[0]
    if tag == "null" and len(node) == 1:
        return None
    if tag == "bool" and len(node) == 2 and type(node[1]) is bool:
        return node[1]
    if tag == "int" and len(node) == 2:
        return integer(node[1])
    if tag == "str" and len(node) == 2 and type(node[1]) is str:
        return node[1]
    if tag == "fraction" and len(node) == 3:
        numerator, denominator = integer(node[1]), integer(node[2])
        if denominator <= 0:
            raise ValueError("typed context rational denominator is not positive")
        result = F(numerator, denominator)
        if result.numerator != numerator or result.denominator != denominator:
            raise ValueError("typed context rational is not reduced")
        return result
    if tag == "binary-float" and len(node) == 2 and type(node[1]) is str:
        value = float.fromhex(node[1])
        if not isfinite(value) or value.hex() != node[1]:
            raise ValueError("typed context binary floating metadata is not canonical")
        return value
    if tag in ("list", "tuple") and len(node) == 2 and type(node[1]) is list:
        items = [unpack(item) for item in node[1]]
        return items if tag == "list" else tuple(items)
    if tag == "dict" and len(node) == 2 and type(node[1]) is list:
        result = {}
        for pair in node[1]:
            if (
                type(pair) is not list or len(pair) != 2
                or type(pair[0]) is not str or pair[0] in result
            ):
                raise ValueError("typed context dictionary repeats or changes a key")
            result[pair[0]] = unpack(pair[1])
        return result
    raise ValueError("typed arithmetic context has an unknown tag or extra fields")


def gate(payload):
    value = unpack(payload)
    if pack(value) != payload:
        raise ValueError("typed arithmetic context did not roundtrip identically")
    return value
