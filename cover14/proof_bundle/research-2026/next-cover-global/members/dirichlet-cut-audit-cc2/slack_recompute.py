"""Independent high-precision recomputation of the DUAL-SLACK-LOCALIZATION endpoint constant.

Different representation from the lead's directed-interval script: exact Fractions for the flow
combinations and mpmath (60 digits) for the geometry/sqrt steps.  Purpose: check the analytic chain

    Lmin = F0 - T*eps - G*eps^2/2                (first+second order cell bound)
    slack = U*N - Lmin                           (r <= U monotonicity)
    sqrt(E) <= sqrt(2U*slack) + (U/r)*sqrt(alignment)   (approximate alignment)
    site_error = eps + rhoerr*diam + sqrt(R)*sqrt(E)
    gauged = site_error + (2*site_error/s)*maxsite      (rotation gauge y(X+)=0, X+ = site 9)

and the coordinate-incidence conventions (48 = 3*nf site-witness rows, then 2 rows per anchor;
anchor j owns rows 48+2j, 48+2j+1; node<14 = site, 14..29 = witness, anchor head = missing -1).
"""
import json, os, heapq, itertools
from fractions import Fraction as F
from mpmath import mp, mpf, sqrt as msqrt, matrix, det as mdet

mp.dps = 60
P = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "lead"))
root = json.loads(open(os.path.join(P, "root-integer-certificate.json")).read())
base = json.loads(open(os.path.join(P, "fixed-anchor-flow-certificate.json")).read())["runs"][0]
flow = json.loads(open(os.path.join(P, "dual-slack-symmetric-flow.json")).read())
cert = json.loads(open(os.path.join(P, "dual-slack-localization-certificate.json")).read())

D = base["incidence_matrix"]; faces = base["faces"]; nf = len(faces); nv = len(D[0])
zz = [[F(str(x)) for x in v] for v in flow["flow_vectors"]]

# ---- reference geometry from the exact root box (midpoints), exactly as the certificate intends
zb = [[F(str(lo)), F(str(hi))] for lo, hi in root["box_dyadic"]]
mid = [(lo + hi) / 2 for lo, hi in zb]
z = mpf(mid[0].numerator) / mpf(mid[0].denominator)
c = mpf(mid[1].numerator) / mpf(mid[1].denominator)
r = mpf(mid[2].numerator) / mpf(mid[2].denominator)
s = msqrt(1 - r * r)
a = (s + z) / 2
t = r + msqrt(r * r - z * z)
b = r + msqrt(r * r - (a - z) ** 2)
d = 1 - msqrt(r * r - c * c)
C = [(sx * a, sy * b) for sx in (-1, 1) for sy in (-1, 1)] + \
    [(sx * c, sy * d) for sx in (-1, 1) for sy in (-1, 1)] + \
    [(-s, mpf(0)), (s, mpf(0)), (z, mpf(0)), (-z, mpf(0)), (mpf(0), -t), (mpf(0), t)]
print("z,c,r =", mp.nstr(z, 12), mp.nstr(c, 12), mp.nstr(r, 12), " s =", mp.nstr(s, 12),
      " |X+|=|site9| =", mp.nstr(msqrt(C[9][0] ** 2 + C[9][1] ** 2), 12), " y(site9) =", mp.nstr(C[9][1], 12))
v1 = (1 + a * a + b * b - r * r) / 2
v2 = (1 + c * c + d * d - r * r) / 2
det = a * d - b * c
px = (v1 * d - v2 * b) / det
py = (a * v2 - c * v1) / det
A = [(s, r), (px, py), (mpf(0), mpf(1)), (-px, py), (-s, r), (-s, -r), (-px, -py),
     (mpf(0), mpf(-1)), (px, -py), (s, -r)]
print("anchor radii:", [mp.nstr(msqrt(x * x + y * y), 10) for x, y in A])

# witness circumcentres (circles through the face's three sites)
W = []
for face in faces:
    p, q, v = [C[i] for i in face]
    u = [q[0] - p[0], q[1] - p[1]]
    w = [v[0] - p[0], v[1] - p[1]]
    de = u[0] * w[1] - u[1] * w[0]
    aa = (q[0] ** 2 + q[1] ** 2 - p[0] ** 2 - p[1] ** 2) / 2
    bb = (v[0] ** 2 + v[1] ** 2 - p[0] ** 2 - p[1] ** 2) / 2
    W.append(((aa * w[1] - u[1] * bb) / de, (u[0] * bb - aa * w[0]) / de))
pts = C + W
print("witness radii:", sorted(mp.nstr(msqrt(x * x + y * y), 10) for x, y in W)[:4], "...")

# ---- flow quantities
lam = [zz[e][0] ** 2 + zz[e][1] ** 2 for e in range(len(zz))]
nrm = [msqrt(mpf(l.numerator) / mpf(l.denominator)) if l else mpf(0) for l in lam]
N = sum(nrm)
alignment = mpf(0)
adj = [[] for _ in range(nv + 1)]
for e, row in enumerate(D):
    if lam[e] == 0:
        continue
    u = row.index(1)
    v = row.index(-1) if -1 in row else nv
    anchor = (e - 3 * nf) // 2 if v == nv else None
    head = pts[v] if v < nv else A[anchor]
    pp = [pts[u][k] - head[k] for k in range(2)]
    ue = [mpf(zz[e][k].numerator) / mpf(zz[e][k].denominator) / nrm[e] for k in range(2)]
    res = [pp[k] - r * ue[k] for k in range(2)]
    alignment += nrm[e] * sum(x * x for x in res)
    cost = 1 / nrm[e]
    adj[u].append((v, cost)); adj[v].append((u, cost))
g = [[-sum(zz[3 * nf + 2 * j + h][k] for h in range(2)) for k in range(2)] for j in range(10)]
F0 = sum(mpf(g[j][k].numerator) / mpf(g[j][k].denominator) * A[j][k] for j in range(10) for k in range(2))
T = sum(abs(mpf(g[j][0].numerator) / mpf(g[j][0].denominator) * (-A[j][1]) +
            mpf(g[j][1].numerator) / mpf(g[j][1].denominator) * A[j][0]) for j in range(10))
G = sum(msqrt(mpf((g[j][0] ** 2 + g[j][1] ** 2).numerator) / mpf((g[j][0] ** 2 + g[j][1] ** 2).denominator))
        for j in range(10))
eps = mpf(1) / 10 ** 6
Lmin = F0 - T * eps - G * eps ** 2 / 2
U = mpf('0.33173203427623414')
slack = U * N - Lmin
rlo = Lmin / N
rhoerr = max(abs(rlo / r - 1), abs(U / r - 1))
diam = max(msqrt((cc[0] - aa[0]) ** 2 + (cc[1] - aa[1]) ** 2) for cc in C for aa in A)
Eroot = msqrt(2 * U * slack) + (U / r) * msqrt(alignment)

dist = [None] * (nv + 1); dist[nv] = mpf(0); pq = [(mpf(0), nv)]
while pq:
    dd, u = heapq.heappop(pq)
    if dd != dist[u]:
        continue
    for v, cost in adj[u]:
        if dist[v] is None or dd + cost < dist[v]:
            dist[v] = dd + cost
            heapq.heappush(pq, (dist[v], v))
R = max(dist[:14])
print("flow JSON site_path_resistances:", flow.get("site_path_resistances"))
print("flow JSON NRmax:", flow.get("NRmax"), " positive_edges:", flow.get("positive_edges"),
      " all_sites_grounded:", flow.get("all_sites_grounded"))
print("my per-site distances:", [mp.nstr(x, 8) for x in dist[:14]])
site_error = eps + rhoerr * diam + msqrt(R) * Eroot
rotation = 2 * site_error / s
maxsite = max(msqrt(cc[0] ** 2 + cc[1] ** 2) for cc in C)
gauged = site_error + rotation * maxsite

print()
print("N          =", mp.nstr(N, 12))
print("F0         =", mp.nstr(F0, 12), " T =", mp.nstr(T, 10), " G =", mp.nstr(G, 10))
print("Lmin       =", mp.nstr(Lmin, 12), " (positive:", Lmin > 0, ")")
print("slack      =", mp.nstr(slack, 12), " rlo =", mp.nstr(rlo, 12))
print("alignment  =", mp.nstr(alignment, 8), " sqrt =", mp.nstr(msqrt(alignment), 8))
print("diam       =", mp.nstr(diam, 12), " rhoerr =", mp.nstr(rhoerr, 8))
print("Eroot      =", mp.nstr(Eroot, 12), " sqrt(R) =", mp.nstr(msqrt(R), 12), " R =", mp.nstr(R, 12))
print("site_error =", mp.nstr(site_error, 12))
print("rotation   =", mp.nstr(rotation, 12), " maxsite =", mp.nstr(maxsite, 12))
print("GAUGED     =", mp.nstr(gauged, 12), " < 4e-5:", gauged < mpf(4) / 10 ** 5)
print("certified gauged interval:", cert["intervals"]["gauged_site_error"])
lo, hi = [F(x) for x in cert["intervals"]["gauged_site_error"]]
print("independent value inside certified interval:",
      lo <= F(mp.nstr(gauged, 30)) <= hi or (float(lo) <= float(gauged) <= float(hi)))
for key, mine in (("N", N), ("F0", F0), ("alignment", alignment),
                  ("site_error", site_error)):
    if key in cert["intervals"]:
        lo, hi = [F(x) for x in cert["intervals"][key]]
        v = F(mp.nstr(mine, 40))
        print(f"  {key}: mine={mp.nstr(mine,10)} interval=({float(lo):.10g},{float(hi):.10g}) inside={lo <= v <= hi}")

