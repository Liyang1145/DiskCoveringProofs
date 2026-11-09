"""Rebuild and replay all parts of the global proof for 26 disks."""

from pathlib import Path
from tempfile import TemporaryDirectory

from check_all import run


def main():
    run("check_all.py")
    with TemporaryDirectory(prefix="n26-global-") as tmp:
        belts = str(Path(tmp) / "belts.tsv")
        chords = str(Path(tmp) / "chords.tsv")
        run("check_belt14.py", "--remaining", belts, "--blocked", chords)
        run("check_transfer14.py", "--belts", belts, "--chords", chords)
    for n, b in ((25, 15), (25, 16), (26, 15), (26, 16), (26, 17)):
        run("check_outer_layers.py", "--disks", str(n), "--boundary", str(b), "--require-complete")
    run("check_outer_layers.py", "--disks", "26", "--boundary", "16", "--candidate-shell",
        "--halfturn", "--candidate-partition", "round4/candidate_halfturn_finish.json", "--require-complete")
    print("PASS: all global exclusion branches and the exact 26-disk cover", flush=True)


if __name__ == "__main__":
    main()
