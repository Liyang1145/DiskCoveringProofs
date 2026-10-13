"""Exact necessary whole-disk area inequality for a nearly saturated boundary ring.

New lens rectangle bound + Jensen inequalities; n21 B12 exclusion is global
over ACTUAL covers, independent of any stored topology enumeration.
"""
from pathlib import Path
from fractions import Fraction as F
from math import isqrt
import argparse
import hashlib
import importlib.util
import json

ROOT=Path(__file__).resolve().parent
if not __debug__:
    raise RuntimeError("Assertions must be enabled")


def sqrt_hi(v,digits=80):
    assert v>=0
    scale=10**digits
    a=isqrt(v.numerator*scale*scale//v.denominator)
    while F(a,scale)**2<v:
        a+=1
    assert F(a,scale)**2>=v
    return F(a,scale)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,default=ROOT/"evidence/n21-B12-lens-area.json")
    args=parser.parse_args()
    assert not args.output.exists()
    cfile=ROOT/"evidence/core-reduction/constants/n21.json"
    constants=json.loads(cfile.read_text())
    assert constants["verified"]
    u=F(constants["radius_upper"]);b=12;n=21
    cap=F(constants["angle_caps"][0],constants["angle_scale"])
    deficit=1-(b-1)*cap
    assert deficit>0 and u<F(1,2)
    source=ROOT.parent/"n13-global/independent_checks.py"
    spec=importlib.util.spec_from_file_location("new_area_trig",source)
    trig=importlib.util.module_from_spec(spec);spec.loader.exec_module(trig)
    def enclosure(iv):
        return F(iv[0],trig.S60),F(iv[1],trig.S60)
    cosd,sind=map(enclosure,trig.trig(F(1,2*b))) # d=pi/B
    cosmin,_=map(enclosure,trig.trig(deficit)) # cos(2 delta_min)
    _,sinmin=map(enclosure,trig.trig(deficit/2)) # sin(delta_min)
    assert sind[0]>0 and cosd[0]>0 and cosmin[0]>0
    lens_monotonic_gap=(2*sinmin[0]-u)*(1-2*u*u)-2*u*u
    assert 2*sinmin[0]>u and lens_monotonic_gap>0
    # h(d) is a genuine positive real; lower proof uses sine upper as a guard.
    assert u*u-sind[1]**2>0
    h=sqrt_hi(u*u-sind[0]**2)
    root3=sqrt_hi(F(3))
    faces=2*n-b-2
    positive=b*sind[0]*cosd[0]*(1-u*u)
    negative=F(3,4)*faces*root3*u*u+b*h*(sind[1]+u*cosmin[1])
    margin=positive-negative
    assert margin>0
    result={"verified":True,"N":n,"B":b,
            "statement":"No arbitrary 21-center closed-unit-disk cover at radius below r_star can have 12 boundary-owner cells",
            "radius_upper":str(u),"boundary_turn_cap":str(cap),"minimum_gap_turns":str(deficit),
            "lens_rectangle_monotonicity_margin":str(lens_monotonic_gap),
            "sine_mean":list(map(str,sind)),"cosine_mean":list(map(str,cosd)),
            "cosine_twice_minimum_gap":list(map(str,cosmin)),
            "sqrt_U_squared_minus_sine_squared_upper":str(h),"sqrt3_upper":str(root3),
            "area_contradiction_margin":str(margin),"area_contradiction_margin_float":float(margin),
            "center_triangle_count":faces,"remaining_boundary_counts":[13,14],
            "scope":"actual-cover geometric exclusion, not all unconstrained auxiliary graph realizations",
            "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "constants_sha256":hashlib.sha256(cfile.read_bytes()).hexdigest(),
            "trig_source_sha256":hashlib.sha256(source.read_bytes()).hexdigest(),
            "global_optimality_proved":False}
    args.output.write_text(json.dumps(result,indent=2),encoding="utf8")
    print("N21 B12 WHOLE ACTUAL-COVER BRANCH EXCLUDED by new boundary-lens area inequality;",
          "strict area margin",float(margin),flush=True)


if __name__=="__main__":
    main()
