"""Exact shared boundary/interior reductions for n21..25; all are necessary only."""
from pathlib import Path
from fractions import Fraction as F
from math import ceil
import argparse
import hashlib
import importlib.util
import json
import mpmath as mp

ROOT=Path(__file__).resolve().parent
if not __debug__:
    raise RuntimeError("Assertions must be enabled")


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,default=ROOT/"evidence/core-reduction")
    args=parser.parse_args()
    assert not args.output.exists()
    args.output.mkdir(parents=True)
    (args.output/"constants").mkdir()
    trigsource=ROOT.parent/"n13-global/independent_checks.py"
    spec=importlib.util.spec_from_file_location("shared_core_trig",trigsource)
    trig=importlib.util.module_from_spec(spec);spec.loader.exec_module(trig)
    sixfile=ROOT.parent/"n21-global/evidence/six-core-exclusion/REPLAY.json"
    six=json.loads(sixfile.read_text())
    assert six["verified"] and F(six["radius"])==F(2771,5000) and six["topology_orbits"]==3
    upper={
        21:F("0.262845072403585"),
        22:F("0.253251459835093"),
        23:F("0.249953776586051"),
        24:F("0.245301650168524"),
        25:F("0.239146311738101")}
    rows=[]
    mp.mp.dps=60
    scale=10**7
    for n,u in upper.items():
        if n==21:
            source=ROOT.parent/"n21-global/evidence/core-root-verified.json"
            lower,hi=json.loads(source.read_text())["r_strict_interval"]
        elif n<25:
            source=ROOT/f"evidence/n{n}/algebraic-check1/root-verified.json"
            lower,hi=json.loads(source.read_text())["r_strict_interval"]
        else:
            source=ROOT/"evidence/n25-algebraic-upper-round2/VERIFIED.json"
            lower,hi=json.loads(source.read_text())["r_strict_interval"]
        assert F(hi)<u<F(1,3)
        approx=mp.mpf(u.numerator)/u.denominator
        bmin=int(mp.floor(mp.pi/mp.asin(approx)))+1
        sine=trig.trig(F(1,2*(bmin-1)))[1]
        assert u<F(sine[0],trig.S60)
        ratio=u/(1-2*u)
        if ratio<F(1,2):
            imin=8
            smallbound=F(1,2)
            used="self-contained elementary r_D(7)>=1/2 (origin plus circle-capacity proof)"
        else:
            assert ratio<F(2771,5000)
            imin=7
            smallbound=F(2771,5000)
            used="three exact six-disk polygon force trees prove r_D(6)>=2771/5000"
        bmax=n-imin
        caps=[int(mp.ceil(mp.asin(k*approx)/mp.pi*scale))+1 for k in (1,2,3)]
        margins=[]
        for k,cap in zip((1,2,3),caps):
            sine=trig.trig(F(cap,2*scale))[1]
            margin=F(sine[0],trig.S60)-k*u
            assert margin>0
            margins.append(str(margin))
        row={"verified":True,"N":n,"radius_upper":str(u),"ratio_core":str(ratio),
             "strict_core_gap":str(smallbound-ratio),"minimum_boundary_cells":bmin,
             "minimum_interior_cells":imin,"maximum_boundary_cells":bmax,
             "families":[[b,n-b] for b in range(bmin,bmax+1)],
             "auxiliary_bound_used":used,"angle_scale":scale,"angle_caps":caps,"sine_margins":margins,
             "radius_root_report_sha256":sha(source),"six_lower_bound_report_sha256":sha(sixfile),
             "trig_source_sha256":sha(trigsource),"source_sha256":sha(Path(__file__)),
             "global_optimality_proved":False}
        (args.output/"constants"/f"n{n}.json").write_text(json.dumps(row,indent=2),encoding="utf8")
        rows.append(row)
        print("N",n,"ACTUAL COVER REDUCTION",row["families"],flush=True)
    (args.output/"VERIFIED.json").write_text(json.dumps({"verified":True,"reductions":rows,
                    "global_optimality_proved_for_any_new_n":False},indent=2),encoding="utf8")


if __name__=="__main__":
    main()
