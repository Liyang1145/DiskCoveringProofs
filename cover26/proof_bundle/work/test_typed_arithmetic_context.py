"""Data-only typed codec controls. These earn zero geometric payments."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import n26_typed_arithmetic_context as codec
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    control = {
        "ordered": (True, 1, F(1), "1", None, -0.0),
        "large": 10**400 + 17,
        "nested": [{"fraction": F(-17, 31)}, []],
    }
    packed = codec.pack(control)
    restored = codec.gate(packed)
    if (
        codec.pack(restored) != packed or list(restored) != list(control)
        or [type(item) for item in restored["ordered"]] != [type(item) for item in control["ordered"]]
    ):
        raise AssertionError("typed codec lost exact scalar types or container order")
    rejected = []

    def reject(label, payload):
        try:
            codec.gate(payload)
        except (ValueError, TypeError, IndexError, OverflowError):
            rejected.append(label)
        else:
            raise AssertionError("invalid typed context accepted: " + label)

    reject("boolean-relabelled-as-integer", ["int", True])
    reject("noncanonical-leading-zero", ["int", "01"])
    reject("nonpositive-denominator", ["fraction", "1", "0"])
    reject("unreduced-rational", ["fraction", "2", "4"])
    reject("duplicate-dictionary-key", ["dict", [["x", ["int", "1"]], ["x", ["int", "2"]]]])
    reject("unknown-executable-tag", ["python", "print('never execute')"])
    reject("hidden-extra-tag-field", ["int", "1", "hidden"])
    reject("nonfinite-floating-metadata", ["binary-float", "nan"])
    reject("noncanonical-floating-metadata", ["binary-float", "0x1p+0"])
    reject("tuple-payload-not-a-wire-list", ["tuple", (["int", "1"],)])
    report = {
        "schema": "N26-data-only-typed-arithmetic-context-regression-v1",
        "exact_scalar_types_container_order_and_negative_zero_preserved": True,
        "invalid_typed_context_controls_rejected": rejected,
        "original_candidate_context_or_geometry_not_verified_by_this_test": True,
        "new_geometric_candidate_payments": 0,
        "tested_codec_sha256": binding.sha(codec.__file__),
        "executed_test_sha256": binding.sha(__file__),
        "global_lower_bound_proved": False, "global_optimality_proved": False,
    }
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
