# -*- coding: utf-8 -*-
"""C853 ridge-feasibility domain: exact identity checks + margins + degeneracies.

Ridge data: delta* = b1-b2, H* = 2r sin(b1+b2), A = b2, B = b1.
Claims checked:
  (i)  H* - 2r|sin delta*| = 4 r cos(max b) sin(min b)                     [exact, > 0]
  (ii) hubnorm residual R = H*^2 - 2 s cos delta* H* + 2r(1-r) = |c9|^2 - (1-r)^2 = -2r*Phi
       with Phi = 2 s sin(b1+b2) cos(b1-b2) - 2 r sin^2(b1+b2) - (1-r),
       equivalently Phi = s(sin2b1 + sin2b2) - 2r sin^2(b1+b2) - (1-r)
              and  r cos(2b1+2b2) + s(sin2b1 + sin2b2) >= 1.
  (iii) Phi >= min(A,B) >= 0.068 > 0 on the whole legal domain (both bounds exact/rational)
  (iv) obtuse-argument condition at the ridge is b1+b2 > pi/2, NOT automatic on the domain
  (v)  minimality of Phi (numeric scan) and the degenerate loci
"""
import mpmath as mp
mp.mp.dps = 30
lines = []
def P(*a):
    s = " ".join(str(x) for x in a); lines.append(s); print(s)

def data(r, b1, b2):
    s = mp.sqrt(1-r*r); phi = mp.asin(r)
    P_ = b1+b2; D_ = b1-b2
    H = 2*r*mp.sin(P_); d = D_
    c9 = mp.matrix([s - H*mp.cos(d), -H*mp.sin(d)])
    res = H*H - 2*s*mp.cos(d)*H + 2*r*(1-r)
    Phi = 2*s*mp.sin(P_)*mp.cos(d) - 2*r*mp.sin(P_)**2 - (1-r)
    Phi_alt = s*(mp.sin(2*b1)+mp.sin(2*b2)) - 2*r*mp.sin(P_)**2 - (1-r)
    Phi_trig = r*mp.cos(2*P_) + s*(mp.sin(2*b1)+mp.sin(2*b2)) - 1
    sep = H - 2*r*abs(mp.sin(d))
    sep_id = 4*r*mp.cos(max(b1, b2))*mp.sin(min(b1, b2))
    return s, phi, H, res, Phi, Phi_alt, Phi_trig, sep, sep_id, c9

P("=" * 78)
P("(i)-(ii) exact identities at sample points")
P("=" * 78)
P("%-24s %-11s %-11s %-11s %-11s" % ("(r,b1,b2)", "R+2rPhi", "Phi-Phi_alt", "Phi-Phi_trig", "sep-sep_id"))
pts = [('0.375', '1.05', '1.05'), ('0.375', '0.60', '0.60'), ('0.375', '0.594', '1.18'),
       ('0.38', '0.61', '0.61'), ('0.38', '1.18', '1.18'), ('0.378', '1.0', '0.7'),
       ('0.375', '1.186', '0.594')]
for (rr, bb1, bb2) in pts:
    r = mp.mpf(rr); b1 = mp.mpf(bb1); b2 = mp.mpf(bb2)
    s, phi, H, res, Phi, Pa, Pt, sep, sep_id, c9 = data(r, b1, b2)
    P("%-24s %-11s %-11s %-11s %-11s" % ("(%s,%s,%s)" % (rr, bb1, bb2),
      mp.nstr(res + 2*r*Phi, 4), mp.nstr(Phi-Pa, 4), mp.nstr(Phi-Pt, 4), mp.nstr(sep-sep_id, 4)))
P("  (all four columns must be ~0; R = |c9|^2-(1-r)^2 = -2r*Phi, sep identity = 4r cos(max) sin(min))")
P("")

P("=" * 78)
P("(iii) Phi over the legal domain; relaxed lower bounds A and B")
P("=" * 78)
def phi_min_scan(r, n=400):
    """numeric min of Phi over b1,b2 in (acos(r)/2, acos(r)] (sampled)"""
    lo = mp.acos(r)/2; hi = mp.acos(r)
    best = None; arg = None
    for i in range(n+1):
        for j in range(n+1):
            b1 = lo + (hi-lo)*mp.mpf(i)/n; b2 = lo + (hi-lo)*mp.mpf(j)/n
            _, _, _, _, Phi, _, _, _, _, _ = data(r, b1, b2)
            if best is None or Phi < best:
                best = Phi; arg = (b1, b2)
    return best, arg
P("%-8s %-14s %-24s %-12s %-12s" % ("r", "min Phi", "at (b1,b2)", "A bound", "B bound"))
for rr in ['0.375', '0.378', '0.38']:
    r = mp.mpf(rr); s = mp.sqrt(1-r*r); cmin = mp.sqrt((1+r)/2)
    A = (1+r)*(mp.sqrt(2*(1-r)) - 1)
    B = (1-r*r)*(4*r*cmin - 8*r**3) - (1-r)
    best, arg = phi_min_scan(r, 160)
    P("%-8s %-14s %-24s %-12s %-12s" % (rr, mp.nstr(best, 8),
      "(%.5f, %.5f)" % (arg[0], arg[1]), mp.nstr(A, 6), mp.nstr(B, 6)))
P("  A = (1+r)(sqrt(2(1-r))-1)  [from the relaxed w=1 endpoint]")
P("  B = (1-r^2)(4r sqrt((1+r)/2) - 8r^3) - (1-r)  [from the relaxed w=2rs endpoint]")
P("  Phi >= min(A,B) rigorously (relaxation: w=sin(b1+b2) in (2rs,1], cos(b1-b2) >= sqrt((1+r)/2))")
P("")
P("  rigorous crude bounds used in the report:")
P("    sqrt(2(1-r)) >= sqrt(1.24) = %.6f  =>  A >= 1.375*(%.6f-1) = %.6f > 0"
  % (float(mp.sqrt(mp.mpf('1.24'))), float(mp.sqrt(mp.mpf('1.24'))), float(mp.mpf('1.375')*(mp.sqrt(mp.mpf('1.24'))-1))))
P("    4r sqrt((1+r)/2) >= 1.5*%.6f = %.6f ; 8r^3 <= 8*0.38^3 = %.6f ; 1-r^2 >= %.6f"
  % (float(mp.sqrt(mp.mpf('0.6875'))), float(1.5*mp.sqrt(mp.mpf('0.6875'))), float(8*mp.mpf('0.38')**3), float(1-mp.mpf('0.38')**2)))
P("    => B >= %.6f*%.6f - 0.625 = %.6f > 0"
  % (float(1-mp.mpf('0.38')**2), float(1.5*mp.sqrt(mp.mpf('0.6875')) - 8*mp.mpf('0.38')**3),
     float((1-mp.mpf('0.38')**2)*(1.5*mp.sqrt(mp.mpf('0.6875')) - 8*mp.mpf('0.38')**3) - 0.625)))
P("")

P("=" * 78)
P("(iv) obtuse face arguments: at the ridge the two sine arguments BOTH equal b1+b2")
P("=" * 78)
P("  arg1 = 2b1 - delta* = b1+b2 , arg2 = 2b2 + delta* = b1+b2  => obtuse iff b1+b2 > pi/2")
P("  b1+b2 ranges over (acos(r), 2 acos(r)] = (pi/2 - asin r, pi - 2 asin r]")
P("  so the obtuse condition FAILS for b1+b2 <= pi/2, e.g. b1=b2 near acos(r)/2:")
for rr in ['0.375', '0.38']:
    r = mp.mpf(rr); lo = mp.acos(r)/2
    b1 = b2 = lo*mp.mpf('1.001')
    P("    r=%s : legal for b1=b2=%.6f ; b1+b2 = %.6f < pi/2 = %.6f  -> ACUTE  (ridge feasible? Phi = %s)"
      % (rr, float(b1), float(b1+b2), float(mp.pi/2),
         mp.nstr(data(r, b1, b2)[4], 6)))
    P("           legal upper end b1=b2=%.6f : b1+b2 = %.6f > pi/2 -> obtuse, Phi = %s"
      % (float(mp.acos(r)), float(2*mp.acos(r)), mp.nstr(data(r, mp.acos(r), mp.acos(r))[4], 6)))
P("")

P("=" * 78)
P("(v) degenerate loci")
P("=" * 78)
P("  sep = 0  <=>  4r cos(max b) sin(min b) = 0  <=>  min b = 0 (outside) or max b = pi/2")
P("     but b <= acos(r) = pi/2 - asin r < pi/2 strictly, so sep > 0 strictly on the chart domain")
P("  Phi = 0  <=>  |c9| = 1-r : numerically NOT attained (see the scan above)")
P("  both face bounds saturated at the ridge, so the H upper endpoint is exactly H* (no slack)")
P("  r = 1/2 is the borderline where the relaxed bound A vanishes (outside r <= 19/50)")

import pathlib
outp = pathlib.Path(__file__).resolve().parent.parent / 'out' / 'p34_ridge_domain.txt'
with open(outp, 'w', encoding='utf-8') as f:
    f.write("\n".join(lines) + "\n")
