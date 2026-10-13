"""Read-only production gates and synthetic prefix/output boundary tests."""
from pathlib import Path
import argparse
import json
import struct
from enumerate_search_stage import stage_gates, inspect_prefix, checked_output, check_bindings, write_new
from stream_catalog import sha

ROOT = Path(__file__).resolve().parent
assert __debug__


def rejects(action):
    try:
        action()
    except (AssertionError, OSError):
        return
    raise AssertionError("bad launch or prefix was accepted")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    args.output.mkdir(parents=True)
    production = []
    for N, B, variant in ((23, 14, "pair"), (24, 13, "outer"), (25, 14, "pair")):
        const, library, table, binary, dependencies = stage_gates(N, B, variant)
        check_bindings(dependencies)
        assert const["N"] == N and [B, N-B] in const["families"]
        production.append({"N": N, "B": B, "variant": variant, "files_checked": len(dependencies),
                           "native_sha256": sha(binary), "library_sha256": sha(table.parent / "LIBRARY.json")})
    negative = []
    rejects(lambda: checked_output(ROOT / "evidence"))
    negative.append("output-outside-registered-volume")
    registry = json.loads((ROOT / "LARGE-OUTPUT-LOCATION.json").read_text())
    location = Path(registry["large_output_root"])
    rejects(lambda: checked_output(location))
    negative.append("output-is-registry-root")
    accepts = location / "launcher-controls-proposal-only-resume1"
    assert checked_output(accepts) == accepts.resolve() and not accepts.exists()
    # This is a synthetic header/size control, not a row-validity theorem.
    folder = args.output / "synthetic-full-prefix-and-truncated-tail"
    folder.mkdir()
    N, B = 23, 14
    faces = 2*N-B-2
    header = b"PAIDRUN1"+struct.pack("<IIIQ", N, B, faces, 2)
    full = header+b"\0"*(2*4*(faces+1))
    for i in range(2):
        (folder / f"run-{i}.bin").write_bytes(full)
    (folder / "run-2.bin").write_bytes(full[:-1])
    prefix = inspect_prefix(folder, N, B, block_size=2)
    assert prefix["full_prefix_runs"] == 2 and len(prefix["excluded_tail_files"]) == 1
    assert prefix["native_exact_comparison_not_yet_done"] and not prefix["search_exhaustion_proved"]
    for label, data in (("extra-bytes", full+b"\0"), ("wrong-N", full[:8]+struct.pack("<I", 24)+full[12:]),
                         ("short-header", full[:20])):
        bad = args.output / label
        bad.mkdir()
        (bad / "run-0.bin").write_bytes(data)
        rejects(lambda bad=bad: inspect_prefix(bad, N, B, block_size=2))
        negative.append(label)
    bad = args.output / "missing-run-zero"
    bad.mkdir()
    (bad / "run-1.bin").write_bytes(full)
    rejects(lambda: inspect_prefix(bad, N, B, block_size=2))
    negative.append("noncontiguous-prefix")
    # Binding checks must reject incorrect bytes; exclusive publication cannot
    # replace an existing successful receipt.
    rejects(lambda: check_bindings({str((folder / "run-0.bin").resolve()): "0"*64}))
    negative.append("changed-binding")
    receipt = args.output / "exclusive-control.json"
    write_new(receipt, {"first": True})
    rejects(lambda: write_new(receipt, {"replacement": True}))
    assert json.loads(receipt.read_text()) == {"first": True}
    negative.append("overwrite-receipt")
    result = {"verified": True, "all_three_production_gates_checked": True,
              "production_gates": production, "prefix_full_tail_partition_checked": True,
              "absolute_cross_volume_bindings_checked": True,
              "negative_controls_rejected": negative,
              "launcher_sha256": sha(ROOT / "enumerate_search_stage.py"),
              "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
              "scope": "launch-input, binding, prefix byte-inspection and publication controls only"}
    write_new(args.output / "VERIFIED.json", result)
    print("Search-stage launcher controls PASS: three exact production gates;",
          len(negative), "bad input/publication boundaries rejected", flush=True)


if __name__ == "__main__":
    main()
