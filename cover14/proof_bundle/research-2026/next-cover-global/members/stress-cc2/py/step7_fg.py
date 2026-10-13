"""step7_fg.py -- evaluate lead/root_scout.py's F,G LITERALLY (verbatim code path) at both roots.
"""
import json, sys
from pathlib import Path
import mpmath as m

m.mp.dps = 60
ROOT = Path(__file__).resolve().parents[5]
OUT = []
def W(s=""):
    OUT.append(str(s)); print(s)

def geom(z, c, r):
    s = m.sqrt(1 - r * r); a = (s + z) / 2; t = r + m.sqrt(r * r - z * z)
    b = r + m.sqrt(r * r - (a - z) ** 2); dd = 1 - m.sqrt(r * r - c * c)
    return a, b, c, dd, s, z, t, r

def fg(z, c, r):
    a, b, c, dd, s, z, t, r = geom(z, c, r)
    v1 = (1 + a * a + b * b - r * r) / 2
    v2 = (1 + c * c + dd * dd - r * r) / 2
    det = a * dd - b * c
    F = (v1 * dd - v2 * b) ** 2 + (a * v2 - c * v1) ** 2 - det * det
    cross = (c - a) * (t - b) - (dd - b) * (-a)
    l1 = (a - c) ** 2 + (b - dd) ** 2; l2 = c * c + (dd - t) ** 2; l3 = a * a + (b - t) ** 2
    G = l1 * l2 * l3 - 4 * r * r * cross * cross
    return F, G

# candidate (z,c,r) triples
scout = json.loads((ROOT / "research-2026/next-cover-global/lead/root-scout.json").read_text())
zn, cn, rn = (m.mpf(x) for x in scout["z_c_r"])
oj = json.loads((ROOT / "research-2026/session2/type14/out/hprec_sol_refined.json").read_text())
th = [m.mpf(x) for x in oj["th"][:7]]; Ro = m.mpf(oj["R"])
oj2 = json.loads((ROOT / "research-2026/session2/type14/out/hprec_sol.json").read_text())
th2 = [m.mpf(x) for x in oj2["th"][:7]]; Ro2 = m.mpf(oj2["R"])

W("== step7: literal F,G of lead/root_scout.py ==")
for tag, (z, c, r) in [
    ("lead root (z=th5_new,c=th2_new,r=r*)", (zn, cn, rn)),
    ("OLD refined (z=th[5],c=th[2],R=refined)", (th[5], th[2], Ro)),
    ("OLD hprec (z=th[5],c=th[2],R=hprec)", (th2[5], th2[2], Ro2)),
    ("OLD refined (z=th[0],c=th[2],R=refined)", (th[0], th[2], Ro)),
    ("OLD refined (z=th[5],c=th[0],R=refined)", (th[5], th[0], Ro)),
]:
    F, G = fg(z, c, r)
    a, b, cc, dd, s, zz, t, rr = geom(z, c, r)
    W("  %-42s F=%s G=%s" % (tag, m.nstr(F, 10), m.nstr(G, 10)))
    W("      -> a=%s b=%s c=%s d=%s t=%s" % (m.nstr(a, 12), m.nstr(b, 12), m.nstr(cc, 12), m.nstr(dd, 12), m.nstr(t, 12)))

W("")
W("(2) NEW expansion: b was set to r+sqrt(r^2-z^2) (same as t). In geom() b is")
W("    r+sqrt(r^2-(a-z)^2) = r+sqrt(r^2 - ((s-z)/2)^2). Are they equal?")
z, c, r = zn, cn, rn
s = m.sqrt(1 - r * r)
b1 = r + m.sqrt(r * r - z * z)
b2 = r + m.sqrt(r * r - ((s - z) / 2) ** 2)
W("    b(z-form) = %s" % m.nstr(b1, 25))
W("    b(geom)   = %s" % m.nstr(b2, 25))
W("    difference = %s" % m.nstr(b1 - b2, 10))
W("(3) does the lead-root expansion satisfy the SAME relation for z & t?")
W("    z=%s  t=b=%s ; r+sqrt(r^2-z^2)=%s" % (m.nstr(z, 20), m.nstr(b2, 20), m.nstr(b1, 20)))

json.dump(dict(zn=m.nstr(zn, 40), cn=m.nstr(cn, 40), rn=m.nstr(rn, 40),
               b_zform=m.nstr(b1, 30), b_geom=m.nstr(b2, 30)), open(Path(__file__).resolve().parents[1] / "evidence/step7_fg.json", "w"), indent=1)
(Path(__file__).resolve().parents[1] / "logs/step7_fg.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/step7_fg.txt")
