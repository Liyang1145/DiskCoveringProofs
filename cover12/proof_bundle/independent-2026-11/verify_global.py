"""Reproduce the computer-assisted proof for the twelve-disk cover."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from fractions import Fraction as Q
from pathlib import Path
import os
import platform
import subprocess
from tempfile import TemporaryDirectory

from balanced import verify as verify_angle_inequality
from exact_angles import check_constants, generate, PI_LO
from exact_directions import directions
from exclude11 import certify_boundary_count
from symmetric import certify_symmetric_root


def verify_separation():
    r = Q(".361103")
    assert 8*Q(".370") < PI_LO
    t, phi = Q(".70"), Q(".242")
    assert (1+t*t-r*r)/(2*t) > 1-phi**2/2+phi**4/24
    x, y = Q("1.10318")/2, Q("1.23118")/2
    assert 2*t*(x-x**3/6) > 2*r
    assert 2*(1-r)*(y-y**3/6) > 2*r


def write_rows(file, rows):
    with file.open("w", encoding="ascii") as out:
        for row in rows:
            print(*row, file=out)


def verify_search(cxx, jobs):
    source = Path(__file__).resolve().parent
    with TemporaryDirectory(prefix="verify-cover12-", dir=source) as folder:
        scratch = Path(folder)
        angle_file = scratch/"angles.txt"
        direction_file = scratch/"directions.txt"
        write_rows(angle_file, generate(96))
        write_rows(direction_file, directions(720))
        obj = scratch/"search.o"
        exe = scratch/("search.exe" if os.name=="nt" else "search")
        # Separate compile and link keeps all build files in the scratch folder.
        flags = ["-std=c++20", "-O2", "-pipe"]
        if platform.machine().lower() in {"amd64", "x86_64"}:
            flags.append("-mpopcnt")
        subprocess.run([cxx, *flags, "-c", str(source/"anchored_search.cpp"), "-o", str(obj)], check=True)
        subprocess.run([cxx, str(obj), "-o", str(exe)], check=True)

        def run(label, args):
            ans = subprocess.run([str(exe), *map(str,args)], capture_output=True, text=True)
            lines = ans.stdout.strip().splitlines()
            if ans.returncode or not lines or lines[0] != "excluded":
                raise RuntimeError(f"{label} remained unresolved.\n{ans.stdout}\n{ans.stderr}")
            return label, lines[1:]

        jobspec = []
        for slot in range(5):
            jobspec.append((f"10 boundary arcs, slot {slot}", [10,720,96,slot,0,0,angle_file]))
        jobspec.append(("9 boundary arcs and one unused boundary disk",
                        [9,720,96,0,0,1,angle_file]))
        for lo,hi in ((0,12),(12,24),(24,36),(36,40),(40,44),(44,48)):
            jobspec.append((f"9 boundary disks, radial bins [{lo},{hi})",
                            [9,720,96,0,0,0,angle_file,direction_file,0,lo,hi]))
        with ThreadPoolExecutor(max_workers=jobs) as pool:
            handles = [pool.submit(run, label, args) for label,args in jobspec]
            for handle in as_completed(handles):
                label, lines = handle.result()
                print(f"{label} — excluded", flush=True)
                for line in lines:
                    print("  "+line, flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cxx", default="g++", help="GCC or Clang C++ compiler")
    parser.add_argument("--jobs", type=int, default=3)
    args = parser.parse_args()
    if args.jobs<1:
        parser.error("--jobs must be positive")
    check_constants()
    verify_separation()
    certify_symmetric_root()
    certify_boundary_count()
    verify_angle_inequality()
    verify_search(args.cxx,args.jobs)
    print("All cases excluded below the constructed radius.", flush=True)
