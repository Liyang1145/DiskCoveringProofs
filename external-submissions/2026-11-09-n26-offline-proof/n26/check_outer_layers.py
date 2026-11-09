"""Rebuild and replay the exterior-shell exclusions and the candidate class."""

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from tempfile import TemporaryDirectory

from verify_fan import require


ROOT = Path(__file__).resolve().parent
ENV = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}
CASES = {
    (25, 15): {0: (5823, 456, 11848), 1: (8075, 91, 1117)},
    (26, 15): {0: (90393, 12569, 313369), 1: (136074, 7064, 274146), 2: (33508, 250, 11883)},
}
COMBINED = {(25, 16): ([2213, 8950, 2800, 1209, 331, 754, 1066, 597,
                        624, 408, 3374, 1952, 1978, 1649, 796, 526], 488, 4968)}
GROUPS = {
    (26,16): [("small",6,0,10000,30612,49,965), ("mid",6,10001,20000,90679,1610,7730),
              ("large_prefix",4,20001,200000,289845,15237,121928),
              ("large_suffix",4,20001,100000,184887,2214,22583)],
    (26,17): [("small",71,0,1000,23639,193,556), ("mid",29,1001,2500,46256,155,1549),
              ("large",15,2501,5000,55984,273,2776),
              ("xl",18,5001,10000,121104,1918,3168),
              ("xxl",23,10001,100000,452516,17627,21999)],
}
REFINED = {(26,15,"_c0"):3129,(26,16,"_mid"):430,(26,16,"_none"):948,
           (26,16,"_large_prefix"):2831,(26,16,"_large_suffix"):712,
           (26,17,"_xl"):125,(26,17,"_xxl"):1160}
ORBITS = {(26,17,"_xxl")}


def run(*args, capture=False):
    result = subprocess.run(args, cwd=ROOT, env=ENV, check=True, text=True,
                            stdout=subprocess.PIPE if capture else None)
    if capture:
        print(result.stdout, end="", flush=True)
        require("truncated=0" in result.stdout, "Truncated shell search")
        return result.stdout


def lines(file, count):
    rows = file.read_bytes().splitlines()
    require(len(rows) == len(set(rows)) == count, f"Unexpected enumeration in {file.name}")


def check(directory,n,b,*,candidate_shell=False,partition=None,halfturn=False,complete=False):
    exe = directory / "outer_layer.exe"
    run("g++", "-Wall", "-Wextra", "-O3", "-std=c++17", str(ROOT / "outer_layer.cpp"), "-o", str(exe))
    classes = directory / "chords.json"
    run(sys.executable, "verify_outer_chords.py", "--classes", str(classes))
    chords, = (d["classes"] for d in json.loads(classes.read_text(encoding="utf-8"))
               if (d["n"], d["b"]) == (n, b))
    key = (n, b)
    if candidate_shell:
        require(key == (26,16) and chords[0] == [], "Unexpected no-chord domain")
        batches = [("_none",[(0,44295)],5554,56354)]
    elif key in COMBINED:
        counts, survivor_count, fill_count = COMBINED[key]
        require(len(chords) == len(counts), "Incomplete combined chord list")
        batches = [("", list(enumerate(counts)), survivor_count, fill_count)]
    elif key in GROUPS:
        batches = []
        seen = set()
        for tag, amount, minimum, maximum, total, survivors, fills in GROUPS[key]:
            path = ROOT / f"shell{n}_b{b}_{tag}_counts.json"
            indices = json.loads(path.read_text(encoding="utf-8"))
            ids = {i for i,_ in indices}
            require(len(indices) == len(ids) == amount and not seen & ids
                    and all(0 <= i < len(chords) and minimum <= c <= maximum for i,c in indices)
                    and sum(c for _,c in indices) == total, "Unexpected chord classes")
            seen.update(ids)
            batches.append((f"_{tag}",indices,survivors,fills))
    else:
        batches = [(f"_c{i}", [(i, s)], k, f) for i, (s, k, f) in CASES[key].items()]
    if key in {(25,15),(25,16),(26,15),(26,17)}:
        covered = {i for _,indices,_,_ in batches for i,_ in indices}
        require(covered == set(range(len(chords))), "Incomplete chord coverage")
    if key == (26,16) and not candidate_shell:
        covered = {i for _,indices,_,_ in batches for i,_ in indices}
        require(chords[0] == [] and covered == set(range(1,len(chords))),
                "Incomplete coverage of 16-arc chorded classes")
    for suffix, indices, survivor_count, fill_count in batches:
        shells, remaining, fills, open_fills = (
            directory / f"{field}.tsv" for field in ("shells", "remaining", "fills", "open_fills")
        )
        nb = ("--disks", str(n), "--boundary", str(b))
        prefix = f"shell{n}_b{b}{suffix}"
        with shells.open("wb") as stream:
            for i, count in indices:
                chunk = directory / f"c{i}.tsv"
                chord_arg = ":".join(f"{u},{v}" for u, v in chords[i]) or "none"
                output = run(str(exe), str(b), str(n), chord_arg, "0", str(chunk), capture=True)
                require(int(re.search(r"representatives=(\d+)", output)[1]) == count, "Shell count changed")
                lines(chunk, count)
                stream.write(chunk.read_bytes())
        shell_count = sum(c for _, c in indices)
        lines(shells, shell_count)
        if not shell_count:
            continue
        run(sys.executable, "verify_shells.py", str(shells), "outer_windows.json",
            f"{prefix}.jsonl.gz", *nb, "--remaining", str(remaining))
        lines(remaining, survivor_count)
        refined = REFINED.get((n,b,suffix))
        if refined is not None:
            narrowed = directory / "refined.tsv"
            run(sys.executable,"verify_shells.py",str(remaining),"outer_windows.json",
                f"{prefix}_refined.jsonl.gz",*nb,"--remaining",str(narrowed))
            remaining, survivor_count = narrowed, refined
            lines(remaining,survivor_count)
        output = run(str(exe), "--fill", str(b), str(n), str(remaining), "0", str(survivor_count), "0",
                     str(fills), capture=True)
        require(int(re.search(r"fillings=(\d+)", output)[1]) == fill_count, "Filling count changed")
        lines(fills, fill_count)
        orbit = ("--orbits",) if candidate_shell or (n,b,suffix) in ORBITS else ()
        run(sys.executable, "verify_shell_fills.py", str(remaining), str(fills), "outer_windows.json",
            f"{prefix}_fills.jsonl.gz", *nb, *orbit, "--remaining", str(open_fills))
        lines(open_fills,4 if candidate_shell else 0)
        if candidate_shell:
            options = ["--shells",str(remaining),"--fills",str(open_fills)]
            if partition is not None:
                options += ["--partition",str(partition.resolve())]
            if halfturn:
                options += ["--halfturn"]
            if complete:
                options += ["--require-complete"]
            run(sys.executable,"verify_candidate_cell.py",*options)
            print("PASS n=26 b=16 no-chord class reduced to the candidate",flush=True)
            return
    excluded = [i for _, indices, _, _ in batches for i, _ in indices]
    print(f"PASS n={n} b={b}: excluded chord classes {excluded}", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--disks", type=int, default=25)
    parser.add_argument("--boundary", type=int, default=15)
    parser.add_argument("--candidate-shell",action="store_true")
    parser.add_argument("--candidate-partition",type=Path)
    parser.add_argument("--halfturn",action="store_true")
    parser.add_argument("--require-complete",action="store_true")
    args = parser.parse_args()
    key = args.disks, args.boundary
    if key not in CASES and key not in COMBINED and key not in GROUPS:
        parser.error("There are no completed chord classes for this combination")
    if args.candidate_shell and key != (26,16):
        parser.error("The candidate shell has 26 disks and 16 arcs")
    if (args.candidate_partition or args.halfturn) and not args.candidate_shell:
        parser.error("Candidate proof options require --candidate-shell")
    if (args.halfturn or args.candidate_shell and args.require_complete) and args.candidate_partition is None:
        parser.error("The angular partition file is required")
    with TemporaryDirectory(prefix="n26-shell-") as path:
        check(Path(path),*key,candidate_shell=args.candidate_shell,partition=args.candidate_partition,
              halfturn=args.halfturn,complete=args.require_complete)
