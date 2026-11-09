"""Rebuild residual b=14 fillings and replay the transferable certificates."""

import argparse
import os
import subprocess
import sys
from pathlib import Path
from tempfile import TemporaryDirectory

from verify_fan import require


ROOT = Path(__file__).resolve().parent
ENV = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}
EXPECTED = {10: 33666, 11: 307702}


def check(layers, directory, belts, chords):
    h = [int(line.split()[1]) for line in belts.read_text(encoding="utf-8").splitlines()]
    require(len(h) == 5565 and set(h) == {10, 11}, "Unexpected residual domain")
    exe = directory / "belt14.exe"
    subprocess.run(
        ["g++", "-Wall", "-Wextra", "-O3", "-std=c++17", str(ROOT / "belt14.cpp"), "-o", str(exe)],
        cwd=ROOT, env=ENV, check=True,
    )
    output = {a: directory / f"h{a}.tsv" for a in (10,11)}
    count = {10: 0, 11: 0}
    with output[10].open("wb") as a, output[11].open("wb") as b, subprocess.Popen(
        [str(exe), "--emit", str(belts), "0", str(len(h)), "1000000", str(chords)],
        stdout=subprocess.PIPE, cwd=ROOT, env=ENV,
    ) as process:
        for line in process.stdout:
            i = int(line.split(b"\t", 1)[0])
            layer = h[i]
            count[layer] += 1
            (a if layer == 10 else b).write(line)
        require(process.wait() == 0 and count == EXPECTED, "Unexpected filling enumeration")
    for layer in layers:
        remaining = directory / f"remaining{layer}.tsv"
        proofs = ROOT / f"belt14_transfer_h{layer}.jsonl.gz"
        subprocess.run(
            [sys.executable, str(ROOT / "verify_transfer14.py"), str(belts), str(output[layer]),
             str(ROOT / "patch14_cuts.json"), str(proofs), "--remaining", str(remaining)],
            cwd=ROOT, env=ENV, check=True,
        )
        require(remaining.stat().st_size == 0, f"Layer {layer} still has unresolved fillings")
        print(f"PASS all residual b=14 fills with layer {layer} are excluded", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--layer", type=int, choices=(10, 11), nargs="+", default=[10,11])
    parser.add_argument("--belts", type=Path, default=ROOT / "belt14_residual.tsv")
    parser.add_argument("--chords", type=Path, default=ROOT / "belt14_residual_chords.tsv")
    args = parser.parse_args()
    with TemporaryDirectory(prefix="n26-transfer-") as directory:
        check(args.layer, Path(directory), args.belts.resolve(), args.chords.resolve())


if __name__ == "__main__":
    main()
