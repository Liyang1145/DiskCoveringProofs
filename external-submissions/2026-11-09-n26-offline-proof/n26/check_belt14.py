"""Regenerate the b=14 topology domains and replay their exact exclusions."""

import argparse
import os
import subprocess
import sys
from pathlib import Path
from tempfile import TemporaryDirectory

from verify_fan import require


ROOT = Path(__file__).resolve().parent
ENV = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}


def run(*args, stdout=None):
    subprocess.run(list(map(str, args)), cwd=ROOT, env=ENV, stdout=stdout, check=True)


def py(script, *args):
    run(sys.executable, ROOT / script, *args)


def rows(file, count):
    data = file.read_text(encoding="utf-8").splitlines()
    require(len(data) == count, f"Unexpected row count in {file.name}")
    return data


def count_fillings(expected, *args):
    result = subprocess.run(list(map(str, args)), cwd=ROOT, env=ENV,
                            capture_output=True, text=True, check=True)
    print(result.stdout, end="", flush=True)
    require(f"fillings={expected}" in result.stdout.splitlines()[0].split(),
            "Unexpected filling count")


def emit_fills(exe, source, states, blocked, destination, include, expected):
    with destination.open("wb") as output:
        for i, line in enumerate(states):
            a, h = map(int, line.split()[:2])
            if include(a, h):
                run(exe, "--emit", source, i, 1, 100000, blocked, stdout=output)
    data = rows(destination, expected)
    require(len(set(data)) == len(data), "Repeated completion")


def verify_complete_fill_set(source, patch, proof, fills, residual):
    py("verify_fills14.py", source, patch, proof, "--fills", fills,
       "--unexcluded", residual)
    require(not residual.read_text(encoding="utf-8").strip(), "An expected closed branch remains open")


def check(directory, full_proof, remaining=None, chord_output=None):
    exe = directory / "belt14.exe"
    run("g++", "-Wall", "-Wextra", "-O3", "-std=c++17", ROOT / "belt14.cpp", "-o", exe)
    py("verify_belt14.py")
    py("verify_seam.py")
    py("verify_outer_chords.py")

    start = directory / "states.tsv"
    run(exe, start)
    rows(start, 35820)
    count_fillings(2337187, exe, "--fill", start)

    patch = ROOT / "patch14_cuts.json"
    first = directory / "patches.tsv"
    py("verify_belt_pruning.py", start, patch, "--remaining", first)
    rows(first, 21745)

    whole9 = directory / "whole9.tsv"
    py("verify_belt_geometry.py", first, patch, ROOT / "belt14_geometry9.json",
       "--remaining", whole9)
    rows(whole9, 21728)

    cycles8 = directory / "cycles8.tsv"
    py("verify_cycles14.py", whole9, ROOT / "belt14_cycles.json", "--all-walks",
       "--remaining", cycles8)
    rows(cycles8, 11904)

    whole10 = directory / "whole10.tsv"
    py("verify_belt_geometry.py", cycles8, patch, ROOT / "belt14_geometry10.json",
       "--remaining", whole10)
    rows(whole10, 11576)

    last = directory / "stage7.tsv"
    py("verify_cycles14.py", whole10, ROOT / "belt14_cycles9.json", "--all-walks",
       "--remaining", last)
    states = rows(last, 5616)

    blocked = directory / "chords.tsv"
    py("verify_fills14.py", last, patch, ROOT / "belt14_chords9.json", "--blocked", blocked)
    rows(blocked, 17)
    count_fillings(481156, exe, "--chords", last, blocked)

    fills = directory / "chordless9.tsv"
    emit_fills(exe, last, states, blocked, fills, lambda _, h: h == 9, 3480)
    verify_complete_fill_set(last, patch, full_proof, fills, directory / "unexcluded9.txt")
    print("PASS all b=14 cases with at most nine inner neighbors are excluded")

    warm = directory / "whole10_warm.tsv"
    py("verify_belt_geometry.py", last, patch, ROOT / "belt14_geometry10_warm.json",
       "--remaining", warm)
    states = rows(warm, 5596)
    final = directory / "remaining.tsv"
    final.write_text("\n".join(line for line in states if int(line.split()[1]) >= 10) + "\n",
                     encoding="utf-8")
    states = rows(final, 5591)
    count_fillings(441582, exe, "--fill", final)
    chords10 = directory / "chords10.tsv"
    py("verify_fills14.py", final, patch, ROOT / "belt14_chords10.json.gz",
       "--blocked", chords10)
    rows(chords10, 702)
    count_fillings(348007, exe, "--chords", final, chords10)
    fills7 = directory / "a7h10.tsv"
    emit_fills(exe, final, states, chords10, fills7, lambda a, h: (a, h) == (7, 10), 45)
    verify_complete_fill_set(final, patch, ROOT / "belt14_a7_h10.json", fills7,
                             directory / "unexcluded7_10.txt")
    print("PASS all b=14 cases with ten inner neighbors and seven apices are excluded")
    fills8 = directory / "a8h10.tsv"
    emit_fills(exe, final, states, chords10, fills8, lambda a, h: (a, h) == (8, 10), 6594)
    verify_complete_fill_set(final, patch, ROOT / "belt14_a8_h10.json.gz", fills8,
                             directory / "unexcluded8_10.txt")
    print("PASS all b=14 cases with ten inner neighbors and eight apices are excluded")

    # Export a new indexed domain, removing whole families just proved
    # impossible. Translate the independently verified chord cuts to its indices.
    residual_belts = directory / "residual.tsv"
    residual_chords = directory / "residual_chords.tsv"
    mapping, keep = {}, []
    for i, line in enumerate(states):
        if tuple(map(int, line.split()[:2])) not in ((7, 10), (8, 10)):
            mapping[i] = len(keep)
            keep.append(line)
    residual_belts.write_text("\n".join(keep) + "\n", encoding="utf-8")
    translated = []
    for line in chords10.read_text(encoding="utf-8").splitlines():
        i, u, v = map(int, line.split())
        if i in mapping:
            translated.append(f"{mapping[i]}\t{u}\t{v}\n")
    residual_chords.write_text("".join(translated), encoding="utf-8")
    rows(residual_belts, 5565)
    count_fillings(341368, exe, "--chords", residual_belts, residual_chords)
    if remaining:
        remaining.write_bytes(residual_belts.read_bytes())
    if chord_output:
        chord_output.write_bytes(residual_chords.read_bytes())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full-proof", type=Path, default=ROOT / "belt14_h9.json.gz")
    parser.add_argument("--remaining", type=Path)
    parser.add_argument("--blocked", type=Path)
    args = parser.parse_args()
    with TemporaryDirectory(prefix="n26-belt-") as name:
        check(Path(name), args.full_proof.resolve(), args.remaining, args.blocked)


if __name__ == "__main__":
    main()
