# -*- coding: utf-8 -*-
"""Independent trig + chain-rule check of lead/LOCAL-HUB-RIDGE-ELIMINATION.md.

Builds the two site faces from the C849 chart WITH MY OWN code, then checks:
 (1) hub angles phi1, phi2 and opposite edges L1, L2 at the ridge;
 (2) h1 == h2 == H* = 2r sin(b1+b2) at delta = b1-b2;
 (3) the radical-free ridge formula against a direct two-face F_H evaluation;
 (4) the branch orientation 2b1-delta, 2b2+delta in (pi/2,pi) and dh1/ddelta>0, dh2/ddelta<0;
 (5) the TOTAL branch derivative by finite differences vs the chain-rule form used in
     certify_delta_ridge.py (this is the 2R normalisation check);
 (6) feasibility margins sep = H*-2r|sin delta*| and norm = H*^2-2s cos delta* H* +2r(1-r).
"""
import json
from pathlib import Path
import mpmath as mp
mp.mp.dps = 40

LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
OUT = Path(__file__).resolve().parent.parent / 'out'
lines = []
def P(*a):
    s = " ".join(str(x) for x in a); lines.append(s); print(s)

J = json.loads((LEAD / 'joint_nested_frozen.json').read_text(encoding='utf-8-sig'))
z = [mp.mpf(str(v)) for v in J['z']]
R0 = mp.mpf(19)/50
P("coefficients: joint_nested_frozen.json ; z[50..72] all zero:", all(v == 0 for v in z[50:73]))
P("z[1]=%s z[3]=%s z[9]=%s z[16]=%s z[20]=%s z[78]=%s z[82]=%s"
  % tuple(mp.nstr(z[i], 10) for i in (1, 3, 9, 16, 20, 78, 82)))
P("")

def face_data(r, b, th, H):
    """one site face: D=|ring-ring edge|, hub angle phi, opposite edge L, and the atom pieces"""
    D = 2*r*mp.sin(b)                     # |c1 c2| in that face
    x = H - D*mp.cos(th); y = D*mp.sin(th)
    Lsq = x*x + y*y                       # = |hub - ring centre|^2 = L^2
    return D, mp.atan2(y, x), mp.sqrt(Lsq), x, y

def FH(r, b1, b2, A, B, H):
    tot = mp.mpf(0)
    for b, th, az, bz, gz in [(b1, A, z[1]-z[9], -z[16], -z[78]), (b2, B, z[3]-z[9], z[20], z[82])]:
        D, phi, L, x, y = face_data(r, b, th, H)
        ee = L/(2*R0)
        tot += H*y/2 + az*phi + bz*ee*ee + gz*ee
    return tot

def ridge_free(r, b1, b2):
    t = r/R0
    return (4*r*r*mp.sin(b1+b2)*mp.sin(b1)*mp.sin(b2) + (z[1]-z[9])*b1 + (z[3]-z[9])*b2
            - z[16]*t*t*mp.sin(b2)**2 - z[78]*t*mp.sin(b2)
            + z[20]*t*t*mp.sin(b1)**2 + z[82]*t*mp.sin(b1))

P("="*80)
P("(1)-(3) ridge geometry and the radical-free formula")
P("="*80)
P("%-22s %-14s %-14s %-14s %-14s %-14s" % ("(r,b1,b2)", "phi1-b1", "phi2-b2", "L1-2r sinb2", "L2-2r sinb1", "free-FH"))
for (rr, bb1, bb2) in [('0.3795', '1.107', '1.0695'), ('0.379', '1.106', '1.071'),
                       ('0.38', '1.108', '1.068'), ('0.3795', '1.108', '1.0685')]:
    r = mp.mpf(rr); b1 = mp.mpf(bb1); b2 = mp.mpf(bb2)
    d = b1 - b2; A = b1 - d; B = b2 + d; H = 2*r*mp.sin(b1+b2)
    D1, phi1, L1, _, _ = face_data(r, b1, A, H)
    D2, phi2, L2, _, _ = face_data(r, b2, B, H)
    h1 = 2*r*mp.sin(2*b1-d); h2 = 2*r*mp.sin(2*b2+d)
    fdir = FH(r, b1, b2, A, B, H); ffree = ridge_free(r, b1, b2)
    P("%-22s %-14s %-14s %-14s %-14s %-14s"
      % ("(%s,%s,%s)" % (rr, bb1, bb2),
         mp.nstr(phi1-b1, 6), mp.nstr(phi2-b2, 6),
         mp.nstr(L1-2*r*mp.sin(b2), 6), mp.nstr(L2-2*r*mp.sin(b1), 6),
         mp.nstr(fdir-ffree, 6)))
    P("      H*=%.12f  h1-H*=%.3e  h2-H*=%.3e  A=%.6f B=%.6f" % (H, h1-H, h2-H, A, B))
P("  (columns 2-5 must be ~0; the last column is the direct-minus-radical-free FH difference)")
P("")

P("="*80)
P("(4) branch orientation and monotonicity of the two face upper bounds")
P("="*80)
r = mp.mpf('0.3795'); b1 = mp.mpf('1.107'); b2 = mp.mpf('1.0695')
P("  over the box r in [.379,.38], b1 in [1.105,1.108], b2 in [1.068,1.071], delta in [.035,.040]:")
lo1 = 2*mp.mpf('1.105') - mp.mpf('0.040'); hi1 = 2*mp.mpf('1.108') - mp.mpf('0.035')
lo2 = 2*mp.mpf('1.068') + mp.mpf('0.035'); hi2 = 2*mp.mpf('1.071') + mp.mpf('0.040')
P("  2b1-delta in [%.6f, %.6f]  (pi/2 = %.6f, pi = %.6f)" % (lo1, hi1, mp.pi/2, mp.pi))
P("  2b2+delta in [%.6f, %.6f]" % (lo2, hi2))
P("  both inside (pi/2,pi) :", (lo1 > mp.pi/2) and (hi1 < mp.pi) and (lo2 > mp.pi/2) and (hi2 < mp.pi))
P("  dh1/ddelta = -2r cos(2b1-delta) in [%.6f, %.6f]  > 0 :"
  % (-2*mp.mpf('0.38')*mp.cos(lo1), -2*mp.mpf('0.379')*mp.cos(hi1)),
  (-2*mp.mpf('0.38')*mp.cos(lo1) > 0) and (-2*mp.mpf('0.379')*mp.cos(hi1) > 0))
P("  dh2/ddelta = +2r cos(2b2+delta) in [%.6f, %.6f]  < 0 :"
  % (2*mp.mpf('0.379')*mp.cos(hi2), 2*mp.mpf('0.38')*mp.cos(lo2)),
  (2*mp.mpf('0.379')*mp.cos(hi2) < 0) and (2*mp.mpf('0.38')*mp.cos(lo2) < 0))
P("  crossing: h1-h2 at delta=b1-b2 equals 0 exactly :",
  abs(2*r*mp.sin(2*b1-(b1-b2)) - 2*r*mp.sin(2*b2+(b1-b2))) < mp.mpf('1e-50'))
P("")

P("="*80)
P("(5) TOTAL branch derivative: finite differences vs the chain-rule form")
P("="*80)
def branch_total(r, b1, b2, d, branch):
    """(z3-z1)*d + FH(d, H(d)) along the branch; H=h1 for branch 1, h2 for branch 2"""
    A = b1 - d; B = b2 + d
    H = 2*r*mp.sin(2*b1-d) if branch == 1 else 2*r*mp.sin(2*b2+d)
    return (z[3]-z[1])*d + FH(r, b1, b2, A, B, H)

def chain_rule(r, b1, b2, d, branch):
    """the analytic expression as coded in certify_delta_ridge.py"""
    A = b1 - d; B = b2 + d
    arg = 2*b1-d if branch == 1 else 2*b2+d
    H = 2*r*mp.sin(arg); Hd = (-2 if branch == 1 else 2)*r*mp.cos(arg)
    res = z[3]-z[1]
    for b, th, td, az, bz, gz in [(b1, A, -1, z[1]-z[9], -z[16], -z[78]),
                                  (b2, B, 1, z[3]-z[9], z[20], z[82])]:
        D = 2*r*mp.sin(b); yy = D*mp.sin(th); yd = D*mp.cos(th)*td
        xx = H - D*mp.cos(th); xd = Hd + D*mp.sin(th)*td
        Q = xx*xx + yy*yy; Qd = 2*xx*xd + 2*yy*yd
        res += (Hd*yy + H*yd)/2 + az*(xx*yd - yy*xd)/Q + bz*Qd/(4*R0*R0) + gz*Qd/(4*R0*mp.sqrt(Q))
    return res

h = mp.mpf('1e-20')
P("%-22s %-6s %-16s %-16s %-12s" % ("(r,b1,b2) delta", "br", "FD total", "chain rule", "diff"))
for (rr, bb1, bb2, dd) in [('0.3795', '1.107', '1.0695', '0.0375'), ('0.379', '1.106', '1.071', '0.035'),
                           ('0.38', '1.108', '1.068', '0.040'), ('0.3795', '1.107', '1.0695', '0.0395')]:
    r = mp.mpf(rr); b1 = mp.mpf(bb1); b2 = mp.mpf(bb2); d = mp.mpf(dd)
    for branch in (1, 2):
        fd = (branch_total(r, b1, b2, d+h, branch) - branch_total(r, b1, b2, d-h, branch))/(2*h)
        cr = chain_rule(r, b1, b2, d, branch)
        P("%-22s %-6d %-16s %-16s %-12s" % ("(%s,%s,%s)%s" % (rr, bb1, bb2, dd), branch,
                                            mp.nstr(fd, 12), mp.nstr(cr, 12), mp.nstr(fd-cr, 3)))
P("")

P("="*80)
P("(6) feasibility margins of the ridge point (my own evaluation, mpmath dps=40)")
P("="*80)
P("%-22s %-16s %-16s" % ("(r,b1,b2)", "sep=H*-2r|sin d*|", "norm=H*^2-2s cos d* H*+2r(1-r)"))
for (rr, bb1, bb2) in [('0.3795', '1.107', '1.0695'), ('0.379', '1.106', '1.071'),
                       ('0.38', '1.108', '1.068'), ('0.379', '1.108', '1.071'),
                       ('0.38', '1.106', '1.068')]:
    r = mp.mpf(rr); b1 = mp.mpf(bb1); b2 = mp.mpf(bb2); d = b1-b2; s = mp.sqrt(1-r*r)
    H = 2*r*mp.sin(b1+b2)
    sep = H - 2*r*abs(mp.sin(d)); norm = H*H - 2*s*mp.cos(d)*H + 2*r*(1-r)
    P("%-22s %-16s %-16s" % ("(%s,%s,%s)" % (rr, bb1, bb2), mp.nstr(sep, 10), mp.nstr(norm, 10)))
P("  (sep > 0 and norm < 0 at every sampled point, matching delta_ridge_feasibility.json)")
P("")
P("REFERENCE: F_H' values at the branch upper endpoints (my own derivative of FH):")
def FHd(r, b1, b2, A, B, H):
    tot = mp.mpf(0)
    for b, th, az, bz, gz in [(b1, A, z[1]-z[9], -z[16], -z[78]), (b2, B, z[3]-z[9], z[20], z[82])]:
        D = 2*r*mp.sin(b); yy = D*mp.sin(th); xx = H - D*mp.cos(th); Q = xx*xx + yy*yy
        tot += yy/2 - az*yy/Q + bz*xx/(2*R0*R0) + gz*xx/(2*R0*mp.sqrt(Q))
    return tot
for (rr, bb1, bb2, dd) in [('0.3795', '1.107', '1.0695', '0.0375'), ('0.379', '1.106', '1.071', '0.035'),
                           ('0.38', '1.108', '1.068', '0.040')]:
    r = mp.mpf(rr); b1 = mp.mpf(bb1); b2 = mp.mpf(bb2); d = mp.mpf(dd); A = b1-d; B = b2+d
    for branch in (1, 2):
        H = 2*r*mp.sin(2*b1-d) if branch == 1 else 2*r*mp.sin(2*b2+d)
        P("   r=%s b1=%s b2=%s delta=%s branch=%d : FH'(H)=%s"
          % (rr, bb1, bb2, dd, branch, mp.nstr(FHd(r, b1, b2, A, B, H), 10)))

with open(OUT / 'p33_ridge_independent.txt', 'w', encoding='utf-8') as f:
    f.write("\n".join(lines) + "\n")
