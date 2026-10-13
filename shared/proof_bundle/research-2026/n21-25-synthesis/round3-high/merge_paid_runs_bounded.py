"""Read-only-input bounded-fan-in finalization for retained exact sorted runs.

Every batch is independently compared against the full union of its inputs.
All original and intermediate runs are retained. This does not establish
search exhaustion: CLI recovery additionally requires a terminal producer,
an intact search-exhausted native phase header, and unchanged launch bindings.
"""
from pathlib import Path
from heapq import heappush, heappop
from hashlib import sha256
import argparse
import ctypes
from ctypes import wintypes
import json
import os
import struct
import time
from paid_binary_residual import BinaryRows
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
WORK = ROOT.parents[2].resolve()
assert __debug__


def read(path):
    return json.loads(Path(path).read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def producer_is_active(pid):
    assert type(pid) is int and pid > 0
    kernel = ctypes.WinDLL("kernel32", use_last_error=True)
    kernel.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
    kernel.OpenProcess.restype = wintypes.HANDLE
    kernel.GetExitCodeProcess.argtypes = [wintypes.HANDLE, ctypes.POINTER(wintypes.DWORD)]
    kernel.CloseHandle.argtypes = [wintypes.HANDLE]
    handle = kernel.OpenProcess(0x1000, False, pid)
    if not handle:
        assert ctypes.get_last_error() == 87, "cannot verify producer absence"
        return False
    try:
        code = wintypes.DWORD()
        assert kernel.GetExitCodeProcess(handle, ctypes.byref(code))
        return code.value == 259
    finally:
        kernel.CloseHandle(handle)


class RawCursor:
    """Producer-side parser; full mask/row validity is checked independently."""
    def __init__(self, path, N, B):
        self.path = Path(path)
        self.stream = self.path.open("rb")
        assert self.stream.read(8) == b"PAIDRUN1"
        fixed = self.stream.read(20)
        assert len(fixed) == 20
        n, b, faces, self.remaining = struct.unpack("<IIIQ", fixed)
        assert (n, b, faces) == (N, B, 2*N-B-2)
        self.count = self.remaining
        self.record = struct.Struct("<"+"I"*(faces+1))
        assert self.path.stat().st_size == 28+self.count*self.record.size
        self.previous = None

    def next(self):
        if not self.remaining:
            assert not self.stream.read(1)
            self.stream.close()
            return None
        raw = self.stream.read(self.record.size)
        assert len(raw) == self.record.size
        row = self.record.unpack(raw)
        stabilizer, code = row[0], row[1:]
        assert stabilizer > 0
        assert self.previous is None or self.previous < code
        self.previous = code
        self.remaining -= 1
        return code, stabilizer, raw


def checked_union(paths, N, B):
    """Acceptor-side complete union using the separately inspected row parser."""
    readers = [BinaryRows(path, run=True) for path in paths]
    assert all((r.header["N"], r.header["B"]) == (N, B) for r in readers)
    rows = [iter(r.rows()) for r in readers]
    queue = []
    def advance(index):
        item = next(rows[index], None)
        if item is not None:
            _, row = item
            heappush(queue, (tuple(row["faces"]), row["stabilizer"], index))
    for i in range(len(rows)):
        advance(i)
    previous = previous_stab = None
    while queue:
        code, stabilizer, i = heappop(queue)
        if code == previous:
            assert stabilizer == previous_stab, "duplicate code has conflicting stabilizers"
        else:
            assert previous is None or previous < code
            previous, previous_stab = code, stabilizer
            yield {"stabilizer": stabilizer, "faces": list(code)}
        advance(i)
    assert all(r.finished for r in readers)


def check_union(paths, target, N, B, *, final=False):
    actual = BinaryRows(target, run=not final)
    assert (actual.header["N"], actual.header["B"]) == (N, B)
    expected = checked_union(paths, N, B)
    count = 0
    for (index, row), reference in zip(actual.rows(), expected, strict=True):
        assert index == count and row == reference
        count += 1
    assert actual.finished and count == actual.header["orbits"]
    return count


def merge_batch(paths, target, N, B, metadata=None):
    target = Path(target)
    temporary = target.with_suffix(target.suffix+".building")
    assert not target.exists() and not temporary.exists()
    assert paths, "empty batches use the explicit empty-final path"
    cursors = [RawCursor(path, N, B) for path in paths]
    queue = []
    for i, cursor in enumerate(cursors):
        item = cursor.next()
        if item is not None:
            code, stabilizer, raw = item
            heappush(queue, (code, i, stabilizer, raw))
    input_count = sum(c.count for c in cursors)
    count = read_count = 0
    previous = previous_stab = None
    with temporary.open("xb") as stream:
        if metadata is None:
            stream.write(b"PAIDRUN1"+struct.pack("<IIIQ", N, B, 2*N-B-2, 0))
            count_offset = 20
        else:
            encoded = json.dumps(metadata, separators=(",", ":"), ensure_ascii=True).encode("ascii")
            stream.write(b"PAIDRSV1"+struct.pack("<IIIIQ", N, B, 2*N-B-2, len(encoded), 0)+encoded)
            count_offset = 24
        while queue:
            code, i, stabilizer, raw = heappop(queue)
            if code == previous:
                assert stabilizer == previous_stab, "inconsistent duplicate stabilizer"
            else:
                assert previous is None or previous < code
                stream.write(raw)
                previous, previous_stab = code, stabilizer
                count += 1
            read_count += 1
            item = cursors[i].next()
            if item is not None:
                newcode, newstab, newraw = item
                heappush(queue, (newcode, i, newstab, newraw))
        assert read_count == input_count
        stream.seek(count_offset)
        stream.write(struct.pack("<Q", count))
        stream.flush()
        os.fsync(stream.fileno())
    # The independent row parser rejects .building by design: publish a
    # proposal-only filename, and the completion report is still withheld.
    temporary.rename(target)
    checked = check_union(paths, target, N, B, final=metadata is not None)
    assert checked == count
    return {"input_files": [str(p) for p in paths], "input_rows": input_count,
            "output_file": str(target), "output_rows": count,
            "complete_independent_union_equality": True, "output_sha256": sha(target)}


def finalize_runs(paths, metadata, out, *, fan_in=32):
    assert type(fan_in) is int and 2 <= fan_in <= 64
    out = Path(out)
    assert not out.exists()
    out.mkdir(parents=True)
    N, B = metadata["N"], metadata["B"]
    initial = [Path(path) for path in paths]
    assert len(initial) == metadata["run_count"]
    assert len(set(initial)) == len(initial)
    expected_rows = 0
    input_hashes = {}
    for path in initial:
        cursor = RawCursor(path, N, B)
        expected_rows += cursor.count
        cursor.stream.close()
        input_hashes[str(path)] = sha(path)
    assert expected_rows == metadata["rows_to_runs"]
    current = initial
    reports = []
    layer = 0
    started = time.monotonic()
    while len(current) > fan_in:
        following = []
        for first in range(0, len(current), fan_in):
            batch = current[first:first+fan_in]
            target = out / f"layer-{layer}-batch-{first//fan_in}.bin"
            receipt = merge_batch(batch, target, N, B)
            receipt["layer"] = layer
            receipt["first_input_index"] = first
            reports.append(receipt)
            following.append(target)
            print("Bounded exact run-union batch", layer, first//fan_in,
                  "inputs", len(batch), "output rows", receipt["output_rows"],
                  "seconds", round(time.monotonic()-started, 1), flush=True)
        assert len(following) == (len(current)+fan_in-1)//fan_in
        current = following
        layer += 1
    target = out / "RESIDUAL.bin"
    finalmeta = dict(metadata, bounded_finalization=True, maximum_batch_input_files=fan_in)
    if current:
        receipt = merge_batch(current, target, N, B, finalmeta)
        reports.append(dict(receipt, layer=layer, final=True))
        count = receipt["output_rows"]
    else:
        assert expected_rows == 0
        encoded = json.dumps(finalmeta, separators=(",", ":"), ensure_ascii=True).encode("ascii")
        with target.open("xb") as stream:
            stream.write(b"PAIDRSV1"+struct.pack("<IIIIQ", N, B, 2*N-B-2, len(encoded), 0)+encoded)
        assert list(BinaryRows(target).rows()) == []
        count = 0
    for path, expected in input_hashes.items():
        assert sha(Path(path)) == expected, "original run changed during finalization"
    result = {"verified": True, "N": N, "B": B, "fan_in": fan_in,
              "original_run_count": len(initial), "original_rows": expected_rows,
              "residual_orbits": count, "catalog_sha256": sha(target),
              "every_batch_complete_union_equality_verified": True,
              "hierarchical_batches_partition_all_previous_layer_inputs": True,
              "original_inputs_hash_checked_before_and_after": True,
              "input_run_sha256": input_hashes, "batch_receipts": reports,
              "source_sha256": sha(Path(__file__)),
              "reader_sha256": sha(ROOT / "paid_binary_residual.py"),
              "search_exhaustion_proved_by_this_merge": False,
              "global_optimality_proved": False,
              "scope": "exact retained-run union only; search exhaustion is a separate prerequisite"}
    return target, result


def phase_metadata(path):
    """Only read a header written after native visit() and final block flush."""
    with Path(path).open("rb") as stream:
        assert stream.read(8) == b"PAIDRSV1"
        fixed = stream.read(24)
        assert len(fixed) == 24
        N, B, F, length, count = struct.unpack("<IIIIQ", fixed)
        assert 3 <= B <= N <= 25 and F == 2*N-B-2 and count == 0
        assert 0 < length <= 64*(1 << 20)
        raw = stream.read(length)
        assert len(raw) == length
        metadata = json.loads(raw.decode("ascii"), object_pairs_hook=no_duplicate_keys)
        assert not stream.read(1), "repair path requires a header-only pre-merge failure"
    assert (metadata["N"], metadata["B"]) == (N, B)
    assert metadata["schema"] == "paid-peeling-residual-binary-v1"
    assert metadata["residual_complete"] is True and metadata["complete"] is False
    assert metadata["root_degree_prune"] is True and metadata["mode"] == "dfs"
    return metadata


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--phase", type=Path, required=True)
    ap.add_argument("--runs", type=Path, required=True)
    ap.add_argument("--bindings", type=Path, required=True)
    ap.add_argument("--terminal-record", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--fan-in", type=int, default=32)
    args = ap.parse_args()
    terminal = read(args.terminal_record)
    assert terminal["native_terminal_observed"] and terminal["native_exit_code"] != 0
    assert terminal["failure_scope"] == "post-search header-only native merge"
    assert terminal["failure_message"] == "REJECTED run header"
    assert not producer_is_active(terminal["native_pid"]), "native search/merge is still alive"
    bindings = read(args.bindings)
    assert terminal["launch_bindings_sha256"] == sha(args.bindings)
    for relative, expected in bindings["files"].items():
        path = (WORK / relative).resolve()
        assert path.is_relative_to(WORK) and sha(path) == expected
    source = ROOT / "paid_stream_storage.inc"
    assert sha(source) == bindings["files"][source.relative_to(WORK).as_posix()]
    binary = (WORK / terminal["native_binary_relative_to_workspace"]).resolve()
    assert binary in (ROOT / "peel_paid_stream.exe", ROOT / "peel_outer_stream.exe")
    assert sha(binary) == terminal["native_binary_sha256"] == bindings["files"][
        binary.relative_to(WORK).as_posix()]
    caller = ROOT / ("peel_outer_stream_kernel.inc" if binary.name == "peel_outer_stream.exe"
                     else "peel_paid_stream_kernel.inc")
    assert sha(caller) == bindings["files"][caller.relative_to(WORK).as_posix()]
    caller_text = caller.read_text(encoding="utf8")
    assert caller_text.index("if(possible(initial))visit(initial,{{boundary,n-b}});else prunes++;") < (
        caller_text.index("auto unique_count=merge_paid_runs(mode);"))
    # Source-phase argument: the caller invokes merge only after visit returns,
    # and this header is serialized only after flush_paid_run has returned.
    source_text = source.read_text(encoding="utf8")
    assert source_text.index(" flush_paid_run();", source_text.index("uint64_t merge_paid_runs")) < (
        source_text.index('out.write("PAIDRSV1",8)'))
    metadata = phase_metadata(args.phase)
    assert metadata["N"] == bindings["N"] and metadata["B"] == bindings["B"]
    assert terminal["native_phase_sha256"] == sha(args.phase)
    controls_path = ROOT / "evidence/bounded-run-merge-controls-final-resume1/VERIFIED.json"
    controls = read(controls_path)
    assert controls["verified"] and controls["520_input_runs_complete_union_compared"]
    assert controls["native_control"]["native_file_quota_failure_reproduced"]
    assert controls["native_control"]["full_reference_set_equality"]
    assert controls["merge_source_sha256"] == sha(Path(__file__))
    assert controls["source_sha256"] == sha(ROOT / "test_bounded_run_merge.py")
    assert sorted(path.name for path in args.runs.iterdir()) == sorted(
        f"run-{i}.bin" for i in range(metadata["run_count"]))
    paths = [args.runs / f"run-{i}.bin" for i in range(metadata["run_count"])]
    target, report = finalize_runs(paths, metadata, args.output, fan_in=args.fan_in)
    report.update(native_phase_sha256=sha(args.phase), terminal_record_sha256=sha(args.terminal_record),
                  launch_bindings_sha256=sha(args.bindings),
                  recovery_controls_sha256=sha(controls_path),
                  native_search_exhausted_source_phase_checked=True,
                  original_failed_outputs_not_rewritten=True,
                  native_search_not_restarted=True,
                  recovered_catalogue_requires_separate_math_and_type_payment=True)
    proof_note = ROOT / "NATIVE-MERGE-RECOVERY.md"
    report["source_phase_written_argument_sha256"] = sha(proof_note)
    report["files"] = dict(bindings["files"])
    for path in (Path(__file__), ROOT / "paid_binary_residual.py", ROOT / "stream_catalog.py",
                 ROOT / "test_bounded_run_merge.py", controls_path, proof_note, args.phase,
                 args.terminal_record, args.bindings):
        resolved = path.resolve()
        assert resolved.is_relative_to(WORK)
        report["files"][resolved.relative_to(WORK).as_posix()] = sha(resolved)
    (args.output / "MERGE-RECOVERY.json").write_text(json.dumps(report, indent=2), encoding="utf8")
    print("Retained native work finalized without restarting search:", target,
          report["residual_orbits"], "unpaid residual types; NOT a global proof", flush=True)


if __name__ == "__main__":
    main()
