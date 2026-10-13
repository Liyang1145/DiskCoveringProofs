"""Rename only the original main to permit a graph diagnostic wrapper."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    source = ROOT / "peel_origin_streamed_collar.cpp"
    target, reportpath = ROOT / "origin_collar_probe_body.inc", ROOT / "origin-probe-source-derivation.json"
    assert not target.exists() and not reportpath.exists()
    before, after = "int main(int argc,char**argv){try{", "int frozen_origin_collar_main(int argc,char**argv){try{"
    text = source.read_text(encoding="utf8")
    assert text.count(before) == 1
    target.write_text(text.replace(before, after), encoding="utf8", newline="\n")
    reportpath.write_text(json.dumps({
        "only_main_name_changed": True, "original_source_sha256": sha(source),
        "derived_source_sha256": sha(target), "source_sha256": sha(Path(__file__)),
        "before": before, "after": after, "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
