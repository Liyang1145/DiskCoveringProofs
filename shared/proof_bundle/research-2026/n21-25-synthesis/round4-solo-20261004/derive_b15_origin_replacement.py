"""New B15 replacement gate/driver; never edits either running production."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    reportpath = ROOT / "b15-origin-replacement-source-derivation.json"
    gatepath, driverpath = ROOT / "b15_origin_replacement_gate.py", ROOT / "run_b15_origin_replacement.py"
    assert not any(p.exists() for p in (reportpath, gatepath, driverpath))
    oldgatepath = ROOT / "origin_production_gate.py"
    oldgate = oldgatepath.read_text(encoding="utf8")
    cutoff = oldgate.index('    failure, inputs = read(failedpath / "NATIVE-TERMINAL.json")')
    gateprefix = oldgate[:cutoff].replace("def origin_gate(controlspath, failedpath, B):",
                                        "def b15_origin_controls_gate(controlspath):").replace(
                                            "    assert B in (16, 17)\n", "")
    gatetail = '''    return files


def b15_replacement_gate(controlspath, previous, B):
    assert B == 15
    files = b15_origin_controls_gate(controlspath)
    from b15_controlled_stop import replacement_readiness
    files.update(replacement_readiness(previous))
    specific = read(ROOT / "n25-B15-origin-replacement-controls-20261005-v1/VERIFIED.json")
    assert specific["verified"] and specific["schema"] == "B15-origin-replacement-controls-v1"
    assert specific["source_sha256"] == sha(ROOT / "test_b15_origin_replacement.py")
    assert specific["origin_controls_sha256"] == sha(controlspath)
    assert specific["all_complete_B15_small_sets_equal"] and specific["all_N25_seed_results_paid_or_retained"]
    unchanged(specific["files_relative_to_workspace"])
    files.update(specific["files_relative_to_workspace"])
    report = read(ROOT / "b15-origin-replacement-source-derivation.json")
    assert report["source_sha256"] == sha(ROOT / "derive_b15_origin_replacement.py")
    assert report["gate_sha256"] == sha(Path(__file__))
    assert report["driver_sha256"] == sha(ROOT / "run_b15_origin_replacement.py")
    original = (ROOT / "run_origin_streamed_search.py").read_text(encoding="utf8")
    for before, after in report["driver_changes"]:
        assert original.count(before) == 1
        original = original.replace(before, after)
    assert original == (ROOT / "run_b15_origin_replacement.py").read_text(encoding="utf8")
    for path in (Path(__file__), ROOT / "b15_controlled_stop.py",
                 ROOT / "derive_b15_origin_replacement.py", ROOT / "b15-origin-replacement-source-derivation.json",
                 ROOT / "n25-B15-origin-replacement-controls-20261005-v1/VERIFIED.json"):
        bind(files, path)
    unchanged(files)
    return files
'''
    gatepath.write_text(gateprefix+gatetail, encoding="utf8", newline="\n")
    originalpath = ROOT / "run_origin_streamed_search.py"
    text = originalpath.read_text(encoding="utf8")
    changes = [
        ("from origin_production_gate import origin_gate",
         "from b15_origin_replacement_gate import b15_replacement_gate"),
        ('    ap.add_argument("--failed-search", type=Path, required=True)',
         '    ap.add_argument("--stopped-search", type=Path, required=True)'),
        ('    assert B in (16, 17), "only the terminal-failed B16/B17 runs are replaced"',
         '    assert B == 15, "only the deliberately stopped owned B15 run is replaced"'),
        ('    files.update(origin_gate(args.origin_controls.resolve(), args.failed_search.resolve(), B))',
         '    files.update(b15_replacement_gate(args.origin_controls.resolve(), args.stopped_search.resolve(), B))'),
        ('    unchanged(files)\n    output.mkdir()',
         '    for path in (ROOT / "b15_origin_replacement_gate.py", ROOT / "b15_controlled_stop.py",\n'
         '                 ROOT / "derive_b15_origin_replacement.py", ROOT / "b15-origin-replacement-source-derivation.json",\n'
         '                 ROOT / "test_b15_origin_replacement.py"):\n'
         '        bind(files, path)\n'
         '    unchanged(files)\n    output.mkdir()'),
    ]
    for before, after in changes:
        assert text.count(before) == 1
        text = text.replace(before, after)
    driverpath.write_text(text, encoding="utf8", newline="\n")
    reportpath.write_text(json.dumps({
        "verified_mechanical_derivation": True, "gate_source_sha256": sha(oldgatepath),
        "gate_prefix_exactly_preserves_all_origin_mathematical_controls": True,
        "original_driver_sha256": sha(originalpath), "driver_changes": changes,
        "driver_sha256": sha(driverpath), "gate_sha256": sha(gatepath),
        "source_sha256": sha(Path(__file__)), "old_running_sources_not_edited": True,
        "previous_prefix_not_claimed_resumed_or_complete": True, "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
