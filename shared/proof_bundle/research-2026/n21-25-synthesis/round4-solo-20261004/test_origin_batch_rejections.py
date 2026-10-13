"""Mechanical preservation and refusal of restricted/unqualified parent catalogs."""
from pathlib import Path
import argparse

ROOT = Path(__file__).resolve().parent
from n25_outer_search import read, publish
from stream_catalog import sha
from batch_origin_collar import parent_gate

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    derivation = read(ROOT / "origin-batch-tools-source-derivation.json")
    assert derivation["verified_mechanical_derivation"]
    assert derivation["source_sha256"] == sha(ROOT / "derive_origin_batch_tools.py")
    for item in derivation["files"]:
        assert sha(ROOT / item["original"]) == item["original_sha256"]
        assert sha(ROOT / item["derived"]) == item["derived_sha256"]
        text = (ROOT / item["original"]).read_text(encoding="utf8")
        for (before, after), count in zip(item["changes"], item["occurrence_counts"], strict=True):
            assert text.count(before) == count
            text = text.replace(before, after)
        assert text == (ROOT / item["derived"]).read_text(encoding="utf8")
    output.mkdir()
    rejected = []
    for label, directory in (
        ("restricted-N25-seed-not-a-whole-family",
         ROOT / "n25-origin-collar-controls-20261005-v1/N25-seed2-allocation0-origin1"),
        ("old-unqualified-schema",
         ROOT / "n25-streamed-collar-controls-20261005-v1/N21-dfs-slab7-sparse0"),
    ):
        try:
            parent_gate(directory / "MANIFEST.json", directory / "NATIVE-TERMINAL.json",
                        directory / "UNION/VERIFIED.json")
        except AssertionError as error:
            if label.startswith("restricted"):
                assert str(error) == "restricted seed is not the complete family"
            rejected.append(label)
        else:
            raise AssertionError(("wrong production-parent scope accepted", label))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "origin-batch-mechanical-and-scope-rejection-controls-v1",
        "original_bounded_memory_and_fresh_exact_replay_logic_preserved": True,
        "negative_controls_rejected": rejected,
        "source_sha256": sha(Path(__file__)),
        "partition_source_sha256": sha(ROOT / "batch_origin_collar.py"),
        "audit_source_sha256": sha(ROOT / "audit_origin_collar_batches.py"),
        "derivation_sha256": sha(ROOT / "origin-batch-tools-source-derivation.json"),
        "actual_complete_N25_production_parent_not_yet_tested": True,
        "not_a_complete_competitor_family_payment": True, "global_optimality_proved": False,
    })
    print("Origin-qualified partition scope controls PASS:", rejected,
          "; full production acceptance still requires an actual complete parent", flush=True)


if __name__ == "__main__":
    main()
