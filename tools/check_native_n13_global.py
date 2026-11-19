#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Replay the native n=13 exact global lower and upper proof components."""
from fractions import Fraction as F
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def b12_arithmetic():
    u,t=F(173323,500000),F(".355")
    def need(ok):
        if not ok:
            raise ArithmeticError("n13 B12 arithmetic comparison")
    def sin_lo(x):
        return x-x**3/6+x**5/120-x**7/5040
    def cos_hi(x):
        return 1-x*x/2+x**4/24
    need(sin_lo(t)>u and 1-t*t/2>2*u and sin_lo(6*t)>2*u)
    need(3*u-1<F(".04") and 1-u-F(".04")>F(".613"))
    need(2*u<F(".694") and F(".734")**2<1-u*u)
    need(8*t<F("3.14") and 2*u<1)
    rows=((613,625,110,487),(625,635,148,449),(635,645,176,414),
          (645,655,199,377),(655,665,218,335),(665,675,235,288),
          (675,685,250,231),(685,694,261,156))
    need(rows[0][0]==613 and rows[-1][1]==694 and
         all(p[1]==q[0] for p,q in zip(rows,rows[1:])))
    for row in rows:
        l,h,a,b=(F(i,1000) for i in row)
        d=h+F(".04")
        need(cos_hi(a)<(1+d*d-u*u)/(2*d) and cos_hi(b)<l/(2*u))
        need(a+F(9,25)*b<t)
    need(12*t<F(34,25)*F("3.14"))


def run():
    def invoke(*args):
        subprocess.run([sys.executable, *map(str,args)],cwd=ROOT,check=True)
    b12_arithmetic()
    invoke("tools/check_native_n13_root.py")
    with TemporaryDirectory(prefix="diskcover-n13-global-") as work:
        work=Path(work)
        invoke("tools/check_native_n13_census.py","--out",work)
        for n in (9,11,10):
            scope="--require-family" if n!=10 else "--require-noncandidate"
            suffix="-noncandidate" if n==10 else ""
            invoke("verification/n13/force_prototype.py",scope,"--quiet",
                   "--census",work/f"n13-B{n}.json",
                   f"verification/n13/force-B{n}{suffix}.json.gz")
        invoke("verification/n13/candidate_tree.py","--census",work/"n13-B10.json")
    return {
        "n":13, "status":"exact_global",
        "radius_exact":"sqrt(t_*)",
        "radius_decimal_interval": [
            "0.346645456927389643467869738193878789537187452966783984053969",
            "0.346645456927389643467869738193878789537187452966783984053970",
        ],
        "candidate_mask_index":712,
        "geometric_non_candidate_exclusions":1678,
        "candidate_branch_nodes":1831,
        "scope":"written analytic reductions and reproducible exact certificates, not Lean",
    }


if __name__=="__main__":
    print(json.dumps(run(),indent=2))
