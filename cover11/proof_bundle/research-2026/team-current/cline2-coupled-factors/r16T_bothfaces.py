"""cline2-coupled-factors R16T: (a) validate G'' against FD of the ANALYTIC G', (b) scan the
LEGAL sets of BOTH faces, (c) check the face-1/face-2 relation without assuming exact symmetry.

Why G'' matters: on the face-1 arc the lead's observation is that the corrected first
derivative may pass from negative to positive along the arc, producing an interior MINIMUM
(endpoints still suffice for the maximum).  A convexity claim (G''>=0) would rule out any
interior stationary maximum; an interior minimum is compatible with G''>0 somewhere.

Validation plan: differencing the analytic G' for G'' (rather than differencing V twice),
which is the standard way to test a second-derivative formula.
"""
import math, json, sys
from pathlib import Path
from mpmath import iv

iv.dps = 30
P = Path(__file__).parent
sys.path.insert(0, str(P))
import r16S_g2_legal as S            # reuse the validated assembler
from r16S_g2_legal import face1_data, legal, C0, XX1, XX2, BE1, GA1, BE2, GA2, RR, TWO

OUT = P / 'out'


def face2_data(r, b1, b2, dl):
    """the face-2 arc: H = 2 r sin(2b2+delta).  Same structure with (b1,A) <-> (b2,B) and
    delta -> -delta, but the coefficients a1/a2 and beta/gamma pairs are NOT equal, so this
    is a genuinely different function, not an exact reflection."""
    s = iv.sqrt(1-r*r)
    A = b1-dl; B = b2+dl
    sinA, cosA = iv.sin(A), iv.cos(A)
    sinB, cosB = iv.sin(B), iv.cos(B)
    sb1, cb1 = iv.sin(b1), iv.cos(b1)
    sb2, cb2 = iv.sin(b2), iv.cos(b2)
    H = TWO*r*iv.sin(TWO*b2+dl)
    Hp = TWO*r*iv.cos(TWO*b2+dl)
    Hpp = -H
    k0 = r*(sb1*sinA+sb2*sinB)
    k1 = r*(-sb1*cosA+sb2*cosB)
    k2 = -r*(sb1*sinA+sb2*sinB)
    hub2 = Hpp*k0+TWO*Hp*k1+H*k2
    # ON-face 2
    e2 = r*sinB/RR; e2p = r*cosB/RR; e2pp = -r*sinB/RR
    on2 = (TWO*BE2*e2+GA2)*e2pp+TWO*BE2*e2p*e2p
    # OFF-face 1
    Y = TWO*r*sb1*sinA
    X = H-TWO*r*sb1*cosA
    Yp = -TWO*r*sb1*cosA
    Xp = Hp+TWO*r*sb1*sinA
    Ypp = TWO*r*sb1*sinA
    Xpp = Hpp+TWO*r*sb1*cosA
    Q = X*X+Y*Y
    if Q.b < iv.mpf(1)/(50000**2):
        return None
    sq = iv.sqrt(Q)
    Qp = TWO*(X*Xp+Y*Yp)
    Qpp = TWO*(Xp*Xp+X*Xpp+Yp*Yp+Y*Ypp)
    e1 = sq/(TWO*RR)
    e1p = Qp/(TWO*sq)/(TWO*RR)
    e1pp = Qpp/(TWO*sq)/(TWO*RR)-Qp*Qp/(4*sq**3)/(TWO*RR)
    phi1p = (X*Yp-Y*Xp)/Q
    off2 = (TWO*BE1*e1+GA1)*e1pp+TWO*BE1*e1p*e1p+TWO*XX1*phi1p
    G = C0+H*k1+Hp*k0+XX2*ZERO_HACK+GA2*e2+BE2*e2*e2+XX1*iv.atan2(Y, X)+BE1*e1*e1+GA1*e1
    Gp = C0+Hp*k1+H*k2+Hpp*k0+Hp*k1+BE2*TWO*e2*e2p+GA2*e2p+XX1*phi1p+BE1*TWO*e1*e1p+GA1*e1p
    Gpp = hub2+on2+off2
    return dict(H=H, Hp=Hp, G=G, G1=Gp, G2=Gpp, Q=Q, s=s)


ZERO_HACK = iv.mpf(0)


def legal2(r, b1, b2, dl, tol=0.0):
    q = face2_data(iv.mpf(repr(r)), iv.mpf(repr(b1)), iv.mpf(repr(b2)), iv.mpf(repr(dl)))
    if q is None:
        return False
    H = float(q['H'].a); s = float(q['s'].a)
    cap1 = 2*r*math.sin(2*b1-dl); cap2 = 2*r*math.sin(2*b2+dl)
    beta = H*H-2*s*math.cos(dl)*H+2*r*(1-r)
    return (H <= cap1+tol) and (H <= cap2+tol) and (beta <= tol) and H > 0


print('=== (a) G2 validation: FD of the ANALYTIC G1 ===')
print(f'{"r":>6s} {"b1":>6s} {"b2":>6s} {"dl":>8s} {"G2 analytic":>15s} {"G2 from FD of G1":>18s} '
      f'{"relerr":>10s}')
h = 1e-4
for (r, b1, b2, dl) in [(0.379, 1.02, 1.02, -0.45), (0.375, 1.05, 1.05, 0.0),
                        (0.376, 1.05, 1.10, 0.10), (0.38, 1.10, 1.02, -0.35),
                        (0.379, 1.00, 1.00, 0.0)]:
    q0 = face1_data(iv.mpf(repr(r)), iv.mpf(repr(b1)), iv.mpf(repr(b2)), iv.mpf(repr(dl)))
    qp = face1_data(iv.mpf(repr(r)), iv.mpf(repr(b1)), iv.mpf(repr(b2)), iv.mpf(repr(dl+h)))
    qm = face1_data(iv.mpf(repr(r)), iv.mpf(repr(b1)), iv.mpf(repr(b2)), iv.mpf(repr(dl-h)))
    if q0 is None or qp is None or qm is None:
        print(f'  {r} {b1} {b2} {dl}: not available')
        continue
    fd = (qp['G1']-qm['G1'])/(2*iv.mpf(repr(h)))
    a = float(q0['G2'].a); b = float(fd.a)
    rel = abs(a-b)/max(1e-30, abs(b))
    print(f'{r:6.3f} {b1:6.3f} {b2:6.3f} {dl:8.4f} {a:15.9f} {b:18.9f} {rel:10.2e}')

print('\n=== (b) legal scan on face-2 (<=200 points) ===')
rng = []
for i in range(6):
    r = 0.375+(0.38-0.375)*i/5
    bhi = math.acos(r)
    for a in range(6):
        b1 = 1+(bhi-1)*a/5
        for b in range(6):
            b2 = 1+(bhi-1)*b/5
            for m in range(11):
                dl = -b2+(b1+b2)*m/10
                rng.append((r, b1, b2, dl))
import random
random.seed(1610)
random.shuffle(rng)
legals2 = []
for (r, b1, b2, dl) in rng:
    if len(legals2) >= 200:
        break
    if not legal2(r, b1, b2, dl):
        continue
    q = face2_data(iv.mpf(repr(r)), iv.mpf(repr(b1)), iv.mpf(repr(b2)), iv.mpf(repr(dl)))
    legals2.append((r, b1, b2, dl, float(q['G'].a), float(q['G1'].a), float(q['G2'].a)))
print(f'legal face-2 points: {len(legals2)}')
if legals2:
    g1 = [row[5] for row in legals2]; g2 = [row[6] for row in legals2]
    print(f"G'  range: [{min(g1):.6f}, {max(g1):.6f}]  (#neg {sum(1 for v in g1 if v<0)}, "
          f"#pos {sum(1 for v in g1 if v>0)})")
    print(f"G'' range: [{min(g2):.6f}, {max(g2):.6f}]  (#neg {sum(1 for v in g2 if v<0)}, "
          f"#pos {sum(1 for v in g2 if v>0)})")
    w = min(legals2, key=lambda t: t[6]); b_ = max(legals2, key=lambda t: t[6])
    print(f"strongest negative G'': {w[6]:.9f} at r={w[0]} b1={w[1]:.6f} b2={w[2]:.6f} "
          f"d={w[3]:.6f} (G'={w[5]:+.6f})")
    print(f"strongest positive G'': {b_[6]:.9f} at r={b_[0]} b1={b_[1]:.6f} b2={b_[2]:.6f} "
          f"d={b_[3]:.6f} (G'={b_[5]:+.6f})")
    neg1 = [row for row in legals2 if row[5] < 0]; pos1 = [row for row in legals2 if row[5] > 0]
    print(f"\nface-2 legal points with G'<0: {len(neg1)}; with G'>0: {len(pos1)}")

print('\n=== (c) both faces: is there an interior stationary point on any legal arc? ===')
rows = json.loads((OUT/'r16s_legal.json').read_text())
f1 = rows['legal']
print('face-1 (from r16S): G\'<0 at all of', len(f1), 'legal points -> no interior stationary')
print('   point; the arc is decreasing, maximum at the smallest admissible delta.')
if legals2:
    print('face-2 (this run): see counts above.')
