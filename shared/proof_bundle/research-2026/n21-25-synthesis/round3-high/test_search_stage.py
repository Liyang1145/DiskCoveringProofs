"""Search-only stages preserve old exact run prefixes and defer all union work."""
from pathlib import Path
import argparse
import json
import subprocess
from merge_paid_runs_bounded import phase_metadata, finalize_runs
from paid_binary_residual import BinaryRows
from stream_catalog import sha

ROOT = Path(__file__).resolve().parent
assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists() and not args.output.is_absolute() and args.output.as_posix().isascii()
    args.output.mkdir(parents=True)
    # The entire recursion is unchanged, only CLI/storage/terminal wording.
    old = (ROOT / "peel_paid_stream_kernel.inc").read_text(encoding="utf8")
    changes = [
        ('#include "paid_matcher.inc"\n#include "paid_stream_storage.inc"',
         '#ifndef PAID_STAGE_OUTER\n#include "paid_matcher.inc"\n#else\n#include "paid_outer_matcher.inc"\n#endif\n#include "paid_search_stage_storage.inc"'),
        ('if(argc!=11)throw runtime_error("usage: paid-peel N B output scale cap2 cap4 cap6 node-limit mode paid-table-or-minus");',
         'if(argc!=13)throw runtime_error("usage: search-stage N B output scale cap2 cap4 cap6 node-limit mode paid-table-or-minus prefix-runs-or-minus prefix-count");'),
        ('load_obstacles(argv[10]);',
         'load_obstacles(argv[10]);\n replay_prefix_directory=argv[11];replay_prefix_count=stoull(argv[12]);\n if((replay_prefix_directory=="-")!=(replay_prefix_count==0))\n  throw runtime_error("prefix directory/count mismatch");'),
        (' auto unique_count=merge_paid_runs(mode);\n cerr<<"RESIDUAL COMPLETE B="<<b<<" calls="<<calls<<" orbits="<<unique_count<<" proof_prunes="<<proof_prunes<<"\\n";',
         ' auto row_count=write_search_phase(mode);\n cerr<<"SEARCH COMPLETE B="<<b<<" calls="<<calls<<" run_rows="<<row_count<<" proof_prunes="<<proof_prunes\n     <<" prefix_runs_compared="<<replay_prefix_runs_compared<<"\\n";'),
    ]
    for before, after in changes:
        assert old.count(before) == 1
        old = old.replace(before, after, 1)
    assert old == (ROOT / "peel_search_stage_kernel.inc").read_text(encoding="utf8")
    controls = json.loads((ROOT / "evidence/bounded-run-merge-controls-final-resume1/VERIFIED.json").read_text())
    assert controls["verified"] and controls["native_control"]["full_reference_set_equality"]
    assert controls["merge_source_sha256"] == sha(ROOT / "merge_paid_runs_bounded.py")
    prefixfolder = Path("evidence/bounded-run-merge-controls-final-resume1/native-N11-B8.bin.runs")
    reference = json.loads((ROOT / "evidence/bounded-run-merge-controls-final-resume1/native-N11-B8-old-reference.json").read_text())
    target = args.output / "replayed-prefix-search.bin"
    proc = subprocess.run([str(ROOT / "peel_search_stage_small.exe"), "11", "8", str(target),
                           "10000000", "2000000", "4200000", "4800000", "0", "dfs", "-",
                           str(prefixfolder), "20"], cwd=ROOT, capture_output=True)
    assert proc.returncode == 0, proc.stderr
    assert not target.exists(), "native stage must not pretend its raw runs are a finished unique catalogue"
    metadata = phase_metadata(Path(str(target)+".building"))
    assert metadata["native_search_only_stage"] and metadata["prefix_runs_replayed_and_compared"] == 20
    assert metadata["run_count"] > 512
    for i in range(20):
        assert sha(Path(str(target)+".runs") / f"run-{i}.bin") == sha(ROOT / prefixfolder / f"run-{i}.bin")
    paths = [Path(str(target)+".runs") / f"run-{i}.bin" for i in range(metadata["run_count"])]
    finalized, report = finalize_runs(paths, metadata, args.output / "finalized", fan_in=16)
    assert [row for _, row in BinaryRows(finalized).rows()] == reference["survivors"]
    # Production block size also completes the same full search.
    prod = args.output / "production-search.bin"
    proc = subprocess.run([str(ROOT / "peel_search_stage.exe"), "11", "8", str(prod),
                           "10000000", "2000000", "4200000", "4800000", "0", "dfs", "-", "-", "0"],
                          cwd=ROOT, capture_output=True)
    assert proc.returncode == 0 and not prod.exists()
    prodmeta = phase_metadata(Path(str(prod)+".building"))
    assert prodmeta["survivor_block_size"] == 100000 and prodmeta["prefix_runs_replayed_and_compared"] == 0
    prodpaths = [Path(str(prod)+".runs") / f"run-{i}.bin" for i in range(prodmeta["run_count"])]
    prodout, _ = finalize_runs(prodpaths, prodmeta, args.output / "production-finalized", fan_in=16)
    assert [row for _, row in BinaryRows(prodout).rows()] == reference["survivors"]
    negative = []
    badprefix = args.output / "bad-prefix"
    badprefix.mkdir()
    raw = (ROOT / prefixfolder / "run-0.bin").read_bytes()
    (badprefix / "run-0.bin").write_bytes(raw[:-1])
    badtarget = args.output / "must-not-finish-prefix.bin"
    proc = subprocess.run([str(ROOT / "peel_search_stage_small.exe"), "11", "8", str(badtarget),
                           "10000000", "2000000", "4200000", "4800000", "0", "dfs", "-",
                           str(badprefix), "1"], cwd=ROOT, capture_output=True)
    assert proc.returncode != 0 and not Path(str(badtarget)+".building").exists()
    negative.append("truncated-old-prefix")
    limited = args.output / "must-not-finish-limited.bin"
    proc = subprocess.run([str(ROOT / "peel_search_stage.exe"), "23", "13", str(limited),
                           "10000000", "804156", "1666328", "2698800", "1", "dfs", "-", "-", "0"],
                          cwd=ROOT, capture_output=True)
    assert proc.returncode != 0 and not Path(str(limited)+".building").exists()
    negative.append("node-limit-does-not-publish-complete-search-phase")
    result = {"verified": True, "search_recursion_mechanically_preserved": True,
              "native_stage_does_not_claim_unique_catalogue": True,
              "more_than_512_run_search_phase_completed": True, "all_20_old_prefix_runs_match_exactly": True,
              "whole_reference_set_matches_after_bounded_finalization": True,
              "production_block_size_also_matches": True,
              "negative_controls_rejected": negative,
              "reference_sha256": sha(ROOT / "evidence/bounded-run-merge-controls-final-resume1/native-N11-B8-old-reference.json"),
              "source_sha256": sha(Path(__file__)),
              "native_sources_sha256": {name: sha(ROOT / name) for name in (
                  "peel_search_stage.cpp", "peel_search_stage_kernel.inc", "paid_search_stage_storage.inc",
                  "paid_matcher.inc", "paid_outer_matcher.inc", "peel_paid_stream_kernel.inc")},
              "binary_sha256": sha(ROOT / "peel_search_stage.exe"),
              "outer_binary_sha256": sha(ROOT / "peel_outer_search_stage.exe"),
              "small_binary_sha256": sha(ROOT / "peel_search_stage_small.exe"),
              "merge_source_sha256": sha(ROOT / "merge_paid_runs_bounded.py"),
              "global_optimality_proved": False, "scope": "resumed-prefix and phase split storage controls only"}
    (args.output / "VERIFIED.json").write_text(json.dumps(result, indent=2), encoding="utf8")
    print("Search-stage controls PASS: old prefix exact, 512+ runs, full reference equal;",
          "no unique-catalogue or global claim before finalization", flush=True)


if __name__ == "__main__":
    main()
