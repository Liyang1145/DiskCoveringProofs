#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Recompute the n=17 necessary topology census with the native n21 peeler."""
from argparse import ArgumentParser
from fractions import Fraction as F
from hashlib import sha256
from itertools import permutations
import json
from pathlib import Path
from subprocess import check_output, run
from tempfile import TemporaryDirectory

ROOT = Path(__file__).resolve().parents[1]
PEEL = "cover21/proof_bundle/research-2026/n21-global/peel21.cpp"
PEEL_SHA = "7063d6fbd45786696873b13c5d8b07e657bcdf47c685b0aae8392876373e53d0"
PEEL_BLOB = "eeb2676d4c92391de22d0a071f43ac69b04f13a1"
U = F("0.29853158925642805986984377443")
SCALE = 10**6
CAPS = (96497, 203666, 353250)
EXPECTED = {
    11:(489,10439,"093c98253b375ea0d7880945979e78b8e0f5d2b578c00c31935c3fa8db84bf1d"),
    12:(631,14583,"96e0d4ea204f930fb5bc1a71e46f8d55a3e42a7be234ea8596b265726cc962ba"),
    13:(200,4992,"e0972f5db2afb98c09922612f07dac6e9a65587fc2a484139d746397cadc186c"),
}


def require(predicate, reason):
    if not predicate:
        raise ArithmeticError(reason)


def bound_caps():
    from math import factorial

    def atan(q,k):
        return sum((-1)**j*F(1,(2*j+1)*q**(2*j+1)) for j in range(k))

    pi_lo=F("3.1415926535")
    require(16*atan(5,12)-4*atan(239,5)>pi_lo,"Machin lower bound")
    for m,c in enumerate(CAPS,1):
        x=pi_lo*c/SCALE
        require(0<x<F(3,2) and 2*c<SCALE, "angle range")
        lo=sum((-1)**j*x**(2*j+1)/factorial(2*j+1) for j in range(6))
        require(lo>m*U,f"{2*m}-rod cap")


def source():
    path=ROOT/PEEL
    raw=path.read_bytes() if path.is_file() else check_output(
        ["git","cat-file","blob",PEEL_BLOB],cwd=ROOT)
    require(sha256(raw).hexdigest()==PEEL_SHA,"bad peeler hash")
    return raw


def verify_record(record,b,mode):
    require(record["complete"] is True and record["screen"] is True and
            (record["N"],record["B"],record["scale"],record["mode"])==(17,b,SCALE,mode) and
            tuple(record["caps"])==CAPS,"wrong census metadata")
    rows=record["survivors"]
    digest=sha256(json.dumps(rows,sort_keys=True,separators=(",",":")).encode()).hexdigest()
    require((len(rows),record["rooted"],digest)==EXPECTED[b] and
            record["orbits"]==len(rows),f"wrong canonical census for B={b}")
    mass=0
    for row in rows:
        st=row["stabilizer"]
        require(st>0 and (2*b)%st==0 and len(row["faces"])==32-b,
                "bad canonical graph")
        mass+=2*b//st
    require(mass==record["rooted"],"dihedral mass mismatch")


def check_candidate(rows):
    # Use brute label equivalence, independent of the peeler's BFS labels.
    from check_native_n17_root import ACTIVE, INACTIVE
    table = {tuple(row["faces"]): i for i,row in enumerate(rows)}
    matched = set()
    for start in range(12):
        for sign in (-1,1):
            base = [(start+sign*i)%12 for i in range(12)]
            for interior in permutations(range(12,17)):
                labels = base+list(interior)
                masks = tuple(sorted(sum(1<<labels[j] for j in face)
                                     for face in ACTIVE+INACTIVE))
                if masks in table:
                    matched.add(table[masks])
    require(matched=={629} and rows[629]["stabilizer"]==2,
            "algebraic candidate does not identify exactly one orbit")


def census(out):
    bound_caps()
    with TemporaryDirectory(prefix="n17-census-") as tmp:
        tmp=Path(tmp)
        cpp=tmp/"native.cpp"
        cpp.write_bytes(source())
        exe=tmp/"peel"
        run(["g++","-std=c++17","-O3",str(cpp),"-o",str(exe)],check=True)
        args=[str(SCALE),*map(str,CAPS)]
        rejected=tmp/"incomplete.json"
        p=run([str(exe),"17","11",str(rejected),*args,"1","dfs"],
              capture_output=True,text=True)
        require(p.returncode!=0 and not rejected.exists() and "NODE LIMIT" in p.stderr,
                "node limit did not fail closed")
        for b in EXPECTED:
            records=[]
            for mode in ("dfs","audit"):
                dest=tmp/f"B{b}-{mode}.json"
                run([str(exe),"17",str(b),str(dest),*args,"50000000",mode],check=True)
                record=json.loads(dest.read_text())
                verify_record(record,b,mode)
                records.append(record)
            require(records[0]["survivors"]==records[1]["survivors"],
                    f"search modes disagree for B={b}")
            if b==12:
                check_candidate(records[0]["survivors"])
            if out:
                out.mkdir(parents=True,exist_ok=True)
                (out/f"n17-B{b}.json").write_text(json.dumps(records[0],indent=2)+"\n")
    print("N17 NECESSARY TOPOLOGY CENSUS PASSED; no metric exclusions claimed")


if __name__=="__main__":
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("--output-directory",type=Path)
    census(parser.parse_args().output_directory)
