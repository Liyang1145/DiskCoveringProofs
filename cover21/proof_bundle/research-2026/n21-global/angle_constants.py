"""Accept n21 angular caps by exact sine bounds, never float asin decisions."""
from pathlib import Path
from fractions import Fraction as F
from math import ceil
import hashlib
import importlib.util
import json
import mpmath as mp

ROOT = Path(__file__).resolve().parent
EV = ROOT/"evidence"
if not __debug__:
    raise RuntimeError("Assertions must be enabled")


def main():
    source = ROOT.parent/"n13-global/independent_checks.py"
    spec = importlib.util.spec_from_file_location("n21_exact_trig",source)
    trig = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(trig)
    report = json.loads((EV/"core-root-verified.json").read_text())
    assert report["verified"]
    upper = F("0.262845072403585")
    assert F(report["r_strict_interval"][1]) < upper < F(1,3)
    mp.mp.dps = 60
    q = 10**7
    proposed = [ceil(mp.asin(k*mp.mpf(str(upper)))/mp.pi*q)+1 for k in (1,2,3)]
    margins = []
    for k,numerator in zip((1,2,3),proposed):
        _,sine = trig.trig(F(numerator,2*q))
        margin = F(sine[0],trig.S60)-k*upper
        assert margin > 0
        margins.append(str(margin))
    _,sn = trig.trig(F(1,22))
    assert upper < F(sn[0],trig.S60) # B>=12 from r*<sin(pi/11).
    caps = [F(v,q) for v in proposed]
    assert 0 < 2*caps[0] < caps[1] < caps[2] < F(1,2)
    data = {"verified":True,"N":21,"radius_upper":str(upper),"angle_scale":q,
            "angle_caps":proposed,"caps_turns":list(map(str,caps)),"sine_margins":margins,
            "minimum_boundary_cells":12,"maximum_boundary_cells":20,
            "families":[[b,21-b] for b in range(12,21)],
            "root_report_sha256":hashlib.sha256((EV/"core-root-verified.json").read_bytes()).hexdigest(),
            "trig_source_sha256":hashlib.sha256(source.read_bytes()).hexdigest(),
            "global_optimality_proved":False}
    (EV/"angle-constants.json").write_text(json.dumps(data,indent=2),encoding="utf8")
    print(json.dumps(data,indent=2),flush=True)


if __name__ == "__main__":
    main()
