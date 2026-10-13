"""Small overlapping fixed-record unions and exact rejection controls."""
from pathlib import Path
from itertools import combinations
import argparse
import json
import struct
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import publish
from merge_paid_runs_bounded import check_union
from audit_n23_B14_restored_union import ranges

assert __debug__


def write_run(path, rows, n=6, b=3, tail=b""):
    faces = 2*n-b-2
    with path.open("xb") as stream:
        stream.write(b"PAIDRUN1"+struct.pack("<IIIQ", n, b, faces, len(rows)))
        for stabilizer, code in rows:
            stream.write(struct.pack("<"+"I"*(faces+1), stabilizer, *code))
        stream.write(tail)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    output.mkdir()
    triples = sorted(sum(1 << vertex for vertex in vertices) for vertices in combinations(range(6), 3))
    codes = [tuple(triples[first:first+7]) for first in range(4)]
    rows = [(1, code) for code in codes]
    a, b, proposed = (output / name for name in ("a.bin", "b.bin", "union.bin"))
    write_run(a, rows[:3])
    write_run(b, rows[1:])
    write_run(proposed, rows)
    assert check_union([a, b], proposed, 6, 3) == 4
    assert ranges(779, 32) == [(first, min(779, first+32)) for first in range(0, 779, 32)]
    assert len(ranges(779, 32)) == 25 and ranges(779, 32)[-1] == (768, 779)
    assert ranges(0, 32) == []
    rejected = []
    for label, altered, tail in (
        ("missing-union-row", rows[:-1], b""),
        ("extra-union-row", rows+[(1, tuple(triples[4:11]))], b""),
        ("duplicate-union-row", rows[:1]+rows, b""),
        ("wrong-union-stabilizer", [(2, codes[0])]+rows[1:], b""),
        ("extra-binary-tail", rows, b"x"),
        ("non-triangle-mask", [(1, (3,)+codes[0][1:])]+rows[1:], b""),
    ):
        target = output / (label+".bin")
        write_run(target, altered, tail=tail)
        try:
            check_union([a, b], target, 6, 3)
        except (AssertionError, ValueError):
            rejected.append(label)
        else:
            raise AssertionError(("corrupt union accepted", label))
    conflict = output / "conflicting-source-stabilizer.bin"
    write_run(conflict, [(2, codes[1]), (1, codes[2])])
    try:
        check_union([a, conflict], proposed, 6, 3)
    except (AssertionError, ValueError):
        rejected.append("conflicting-duplicate-input-stabilizer")
    else:
        raise AssertionError("conflicting duplicate source stabilizer accepted")
    for label, count, fan in (
        ("boolean-run-count", True, 32), ("negative-run-count", -1, 32),
        ("invalid-fan-in", 779, 1), ("unbounded-fan-in", 779, 65),
    ):
        try:
            ranges(count, fan)
        except AssertionError:
            rejected.append(label)
        else:
            raise AssertionError(("bad input partition accepted", label))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "restored-B14-union-adapter-finite-controls-v1",
        "small_overlapping_fixed_record_union_positive": True,
        "all_779_input_indices_partition_once_in_25_at_most32_batches": True,
        "negative_controls_rejected": rejected,
        "source_sha256": sha(Path(__file__)),
        "adapter_source_sha256": sha(ROOT / "audit_n23_B14_restored_union.py"),
        "frozen_merge_source_sha256": sha(HIGH / "merge_paid_runs_bounded.py"),
        "frozen_reader_source_sha256": sha(HIGH / "paid_binary_residual.py"),
        "functional_binary_fixtures_not_geometric_types_or_native_search_evidence": True,
        "not_a_production_union_or_lower_bound_payment": True, "global_optimality_proved": False,
    })
    print("Restored B14 full-union adapter controls PASS:", len(rejected), "rejections", flush=True)


if __name__ == "__main__":
    main()
