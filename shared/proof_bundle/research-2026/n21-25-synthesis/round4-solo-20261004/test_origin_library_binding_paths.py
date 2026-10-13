"""Real relative/absolute binding agreement and corruption/escape controls."""
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parent
WORK = ROOT.parents[2]
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import publish
from audit_complete_origin_library_transport_v2 import absolute_library_bindings

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    source = ROOT / "LINKED-FILLING-EXACT-COLLAR-TRANSPORT.md"
    relative, digest = source.relative_to(WORK).as_posix(), sha(source)
    assert absolute_library_bindings({relative: digest}) == {str(source.resolve()): digest}
    assert absolute_library_bindings({relative.replace("/", "\\"): digest}) == {str(source.resolve()): digest}
    rejected = []
    cases = (
        ("absolute-name-in-relative-ledger", {str(source): digest}),
        ("escape-original-workspace", {"../outside-proof.txt": digest}),
        ("missing-real-file", {relative+".missing": digest}),
        ("wrong-current-file-bytes", {relative: "0"*64}),
        ("non-string-path", {True: digest}),
        ("duplicate-resolved-file", {relative: digest, relative.replace("/", "\\"): digest}),
    )
    for label, files in cases:
        try:
            absolute_library_bindings(files)
        except (AssertionError, TypeError, FileNotFoundError):
            rejected.append(label)
        else:
            raise AssertionError(("bad relative proof binding accepted", label))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "origin-library-relative-binding-normalization-controls-v1",
        "actual_workspace_relative_names_resolve_to_original_absolute_bytes": True,
        "both_path_separator_styles_checked": True, "negative_controls_rejected": rejected,
        "source_sha256": sha(Path(__file__)),
        "audit_source_sha256": sha(ROOT / "audit_complete_origin_library_transport_v2.py"),
        "all_mathematical_replays_and_complete_parent_merge_still_required": True,
        "global_optimality_proved": False,
    })
    print("Library original-workspace binding controls PASS:", len(rejected), "rejections", flush=True)


if __name__ == "__main__":
    main()
