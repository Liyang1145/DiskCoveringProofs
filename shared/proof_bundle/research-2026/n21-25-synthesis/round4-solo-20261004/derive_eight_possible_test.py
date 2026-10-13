"""Rename the enum entry point, without macro interference in frozen includes."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    source = ROOT / "peel_eight_rod_collar.cpp"
    target = ROOT / "eight_collar_probe_body.inc"
    report = ROOT / "eight-possible-test-source-derivation.json"
    assert not target.exists() and not report.exists()
    old = source.read_text(encoding="utf8")
    before = "int main(int argc,char**argv){try{"
    after = "int frozen_eight_collar_main(int argc,char**argv){try{"
    assert old.count(before) == 1 and after not in old
    new = old.replace(before, after, 1)
    assert new.replace(after, before, 1) == old
    target.write_text(new, encoding="utf8", newline="\n")
    report.write_text(json.dumps({
        "native_source_sha256": sha(source), "probe_body_sha256": sha(target),
        "only_entrypoint_name_changed": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
