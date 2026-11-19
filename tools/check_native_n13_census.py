#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Exact necessary-topology census for the native n=13 branch reduction."""
from argparse import ArgumentParser
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory


ROOT = Path(__file__).resolve().parents[1]
PEEL = "cover21/proof_bundle/research-2026/n21-global/peel21.cpp"
PEEL_SHA = "7063d6fbd45786696873b13c5d8b07e657bcdf47c685b0aae8392876373e53d0"
PEEL_BLOB = "eeb2676d4c92391de22d0a071f43ac69b04f13a1"
U = F(173323, 500000)
SCALE, CAP2, CAP4, CAP6 = 1000000, 112680, 244000, 500000
EXPECTED = {9: (610, 10128), 10: (718, 13495), 11: (351, 7282)}


def require(ok, message):
    if not ok:
        raise ArithmeticError(message)


def check_constants():
    # Q(x) is a lower bound for sin(x) throughout this check.
    Q = lambda x: x - x**3/6 + x**5/120 - x**7/5040
    pi_lo = F("3.1415926535")
    require(Q(pi_lo*CAP2/SCALE) > U, "2-rod cap")
    require(Q(pi_lo*CAP4/SCALE) > 2*U, "4-rod cap")
    require(3*U > 1 and 2*CAP6 == SCALE, "6-rod cap must be disabled")
    T = F(".355")
    require(Q(T) > U and Q(6*T) > 2*U and 1-T*T/2 > 2*U,
            "long outer chord exclusion")


def source():
    path = ROOT / PEEL
    if path.is_file():
        raw = path.read_bytes()
    else:
        raw = subprocess.check_output(["git", "cat-file", "blob", PEEL_BLOB], cwd=ROOT)
    require(sha256(raw).hexdigest() == PEEL_SHA, "native peeler digest mismatch")
    data = raw.decode()
    patches = (
        # A half-turn cap is vacuous. Never use a six-rod upper chord
        # longer than the diameter as if it defined an inverse sine.
        ("else if(reach2&ends)cap=caps[2];",
         "else if(reach2&ends && caps[2]<scale/2)cap=caps[2];"),
        ("caps[2]>=scale/2", "caps[2]>scale/2"),
        # Independently proved in the native n=13 geometry note.
        (" if(!screen)return true;", """ if(!screen)return true;
 for(int i=0;i<b;i++)for(int j=i+1;j<b;j++)
  if(min(j-i,b-j+i)>=b-7 && (s.adjacency[i]>>j&1))return false;"""),
    )
    for old,new in patches:
        require(data.count(old) == 1, f"patch mismatch at {old}")
        data = data.replace(old,new)
    return data


def run(out=None):
    check_constants()
    results = {}
    with TemporaryDirectory(prefix="diskcover-n13-census-") as tmp:
        tmp = Path(tmp)
        cpp = tmp/"peel13.cpp"
        exe = tmp/"peel13"
        cpp.write_text(source(), encoding="utf-8")
        subprocess.run(["g++", "-O3", "-std=c++17", str(cpp), "-o", str(exe)],
                       check=True)
        # Known Catalan case: triangulations of a fixed labeled hexagon.
        small = tmp/"hexagon.json"
        subprocess.run([str(exe), "6", "6", str(small), str(SCALE),
                        str(CAP2), str(CAP4), str(CAP6), "100000", "noscreen"],
                       check=True)
        d = json.loads(small.read_text())
        require(d["complete"] is True and d["screen"] is False and
                d["orbits"]==3 and d["rooted"]==14 and
                sorted(r["stabilizer"] for r in d["survivors"])==[2,2,6],
                "hexagon Catalan regression")
        # Artificially exhaust the node allowance: never yield a complete file.
        absent = tmp/"should-not-exist.json"
        fail = subprocess.run([str(exe), "13", "9", str(absent), str(SCALE),
                               str(CAP2), str(CAP4), str(CAP6), "1", "dfs"],
                              capture_output=True, text=True)
        require(fail.returncode!=0 and "limit" in fail.stderr.lower()
                and not absent.exists(), "node limit was not fail-closed")
        for B, (orbits, rooted) in EXPECTED.items():
            pair = []
            for mode in ("dfs", "audit"):
                path = tmp/f"{B}-{mode}.json"
                subprocess.run([str(exe), "13", str(B), str(path), str(SCALE),
                                str(CAP2), str(CAP4), str(CAP6), "50000000", mode],
                               check=True)
                d = json.loads(path.read_text())
                require(d["complete"] is True and d["screen"] is True and d["N"]==13
                        and d["B"]==B and d["scale"]==SCALE and d["mode"]==mode
                        and d["caps"]==[CAP2,CAP4,CAP6], "wrong census metadata")
                require(d["orbits"]==len(d["survivors"])==orbits and
                        d["rooted"]==rooted, "unexpected branch counts")
                rows = d["survivors"]
                for row in rows:
                    st = row["stabilizer"]
                    require(st > 0 and (2*B)%st==0,"invalid dihedral stabilizer")
                    require(len(row["faces"]) == 24-B, "invalid face count")
                require(sum((2*B)//r["stabilizer"] for r in rows)==rooted,
                        "dihedral mass mismatch")
                pair.append(d)
            require(pair[0]["survivors"] == pair[1]["survivors"],
                    "canonical face lists disagree")
            results[B] = pair[0]
            print(f"n13 B={B}: {orbits} necessary-condition survivors, {rooted} rooted")
    if out is not None:
        out.mkdir(parents=True, exist_ok=True)
        for B, data in results.items():
            (out/f"n13-B{B}.json").write_text(json.dumps(data, indent=2)+"\n")
    print("N13 NECESSARY TOPOLOGY CENSUS PASSED; no metric exclusions claimed")


if __name__ == "__main__":
    cli = ArgumentParser(description=__doc__)
    cli.add_argument("--out", type=Path, help="optional fresh census output directory")
    run(cli.parse_args().out)
