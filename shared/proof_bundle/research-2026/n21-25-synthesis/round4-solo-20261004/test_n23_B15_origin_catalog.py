"""Finite ledger corruptions and parser controls; never production payments."""
from io import StringIO
from itertools import combinations
from pathlib import Path
from fractions import Fraction as F
import argparse
import json
import random
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import Catalog, sha
from n25_outer_search import read, publish
from audit_n23_B15_origin_catalog import independent_exposure, scan_rows, radius_gate, N, B
from refine_collar_origin import exposed_mask
from small_order_cover_origin import classify

assert __debug__


def encoded(rows):
    return "".join(json.dumps(row, separators=(",", ":"))+"\n" for row in rows)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    output.mkdir()
    corepath = ROOT / "n23-n24-archive-core-inputs-20261005-v1/n23/core-system.json"
    candidate = read(corepath)
    assert (candidate["N"], candidate["B"]) == (N, B)
    real_faces = sorted(sum(1 << v for v in face) for face in candidate["all_faces"])
    knownmask = independent_exposure(real_faces)
    assert knownmask.bit_count() == N-1
    assert knownmask == exposed_mask(N, B, real_faces)
    # The second row is a face-array functional fixture, NOT a planar type
    # or a claim of geometric realizability / a necessary-family member.
    fake_faces = [3 | (1 << v) for v in range(B, N)]
    fake_faces += [sum(1 << v for v in vertices)
                   for vertices in list(combinations(range(B), 3))[:21]]
    fake_faces.sort()
    assert len(fake_faces) == 2*N-B-2
    rows = [(0, {"stabilizer": 1, "faces": real_faces}),
            (1, {"stabilizer": 1, "faces": fake_faces})]
    paid = [{"index": 1, "exposed_mask": (1 << N)-1}]
    pending = [{"index": 0, "exposed_mask": knownmask}]
    result = scan_rows(iter(rows), StringIO(encoded(paid)), StringIO(encoded(pending)), 2)
    assert result["actual_cover_origin_obstructions"] == result["pending_full_types"] == 1
    rejected = []

    def reject(label, source=rows, pay=paid, rest=pending, total=2, raw_pay=None):
        try:
            scan_rows(iter(source), StringIO(encoded(pay) if raw_pay is None else raw_pay),
                      StringIO(encoded(rest)), total)
        except (AssertionError, json.JSONDecodeError):
            rejected.append(label)
        else:
            raise AssertionError(("accepted corrupt control", label))

    reject("missing-obstruction", pay=[])
    reject("missing-pending", rest=[])
    reject("duplicate-obstruction", pay=paid+paid)
    reject("extra-pending", rest=pending+pending)
    reject("wrong-exposure-mask", pay=[{"index": 1, "exposed_mask": knownmask}])
    reject("wrong-paid-index", pay=[{"index": 0, "exposed_mask": (1 << N)-1}])
    reject("statuses-swapped", pay=pending, rest=paid)
    reject("source-index-gap", source=[(0, rows[0][1]), (2, rows[1][1])])
    reject("false-declared-total", total=3)
    reject("duplicate-ledger-key", raw_pay='{"index":1,"index":1,"exposed_mask":8388607}\n')
    reject("truncated-ledger-json", raw_pay='{"index":1')
    for value in (F(1, 4), F(13, 50), F(0)):
        try:
            radius_gate(value)
        except AssertionError:
            rejected.append("radius-"+str(value))
        else:
            raise AssertionError("accepted a non-strict or nonpositive radius")
    internal_only = sorted({3 | (1 << v) for v in range(B, N-1)}
                           | {(1 << B) | (1 << (B+1)) | (1 << (N-1))})
    assert independent_exposure(internal_only).bit_count() == N-1
    assert max(mask.bit_length() for mask in internal_only) == N
    rng = random.Random(23151005)
    for _ in range(200):
        faces = sorted({sum(1 << v for v in rng.sample(range(N), 3))
                        for _ in range(rng.randrange(1, 60))})
        got = independent_exposure(faces)
        assert got == exposed_mask(N, B, faces)
        assert got == classify(N, B, faces, F(249953776586051, 10**15))["exposed_label_mask"]
    for label, invalid in (
        ("oversized-face-mask", [1 << N | 3]),
        ("non-triangle", [3]),
        ("duplicate-faces", [7, 7]),
        ("boolean-face", [True]),
    ):
        try:
            independent_exposure(invalid)
        except AssertionError:
            rejected.append(label)
        else:
            raise AssertionError(("accepted invalid face", label))
    header = {"complete": True, "N": N, "B": B, "orbits": 2}
    valid = {**header, "survivors": [row for _, row in rows]}
    goodpath = output / "FINITE-PARSER-POSITIVE.json"
    goodpath.write_text(json.dumps(valid, separators=(",", ":")), encoding="ascii")
    reader = Catalog(goodpath)
    assert list(reader.rows()) == rows and reader.finished
    corrupt = (
        ("parser-declared-orbit-count", {**valid, "orbits": 3}),
        ("parser-incomplete-header", {**valid, "complete": False}),
        ("parser-face-count", {**valid, "survivors": [{"stabilizer": 1, "faces": [7]}, rows[1][1]]}),
        ("parser-nonpositive-stabilizer", {**valid, "survivors": [
            {"stabilizer": 0, "faces": real_faces}, rows[1][1]]}),
    )
    for label, payload in corrupt:
        path = output / (label+".json")
        path.write_text(json.dumps(payload, separators=(",", ":")), encoding="ascii")
        reader = None
        try:
            reader = Catalog(path)
            list(reader.rows())
        except AssertionError:
            rejected.append(label)
        else:
            raise AssertionError(("accepted corrupt catalog", label))
        finally:
            if reader is not None:
                reader.stream.close()
    for label, suffix in (("parser-extra-tail", "x"), ("parser-truncated", None)):
        text = goodpath.read_text(encoding="ascii")
        path = output / (label+".json")
        path.write_text(text+suffix if suffix else text[:-2], encoding="ascii")
        reader = None
        try:
            reader = Catalog(path)
            list(reader.rows())
        except (AssertionError, json.JSONDecodeError):
            rejected.append(label)
        else:
            raise AssertionError(("accepted corrupt catalog", label))
        finally:
            if reader is not None:
                reader.stream.close()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "finite-N23-B15-origin-full-catalog-audit-controls-v1",
        "recorded_attaining_full_graph_kept_pending": True,
        "pure_internal_triangle_does_not_expose_its_hidden_label": True,
        "independent_random_exposure_comparisons": 200,
        "finite_two_row_ledger_partition_and_complete_parser_positive": True,
        "negative_controls_rejected": rejected,
        "source_sha256": sha(Path(__file__)),
        "acceptor_source_sha256": sha(ROOT / "audit_n23_B15_origin_catalog.py"),
        "proposer_source_sha256": sha(ROOT / "partition_n23_B15_origin_catalog.py"),
        "recorded_core_sha256": sha(corepath),
        "not_a_production_catalog_scan_or_payment": True, "global_optimality_proved": False,
    })
    print("N23/B15 full-catalog origin audit controls PASS:", len(rejected),
          "rejections; recorded attaining graph retained", flush=True)


if __name__ == "__main__":
    main()
