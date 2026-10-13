"""root-cc2 stress-audit: decisive checks on the two anomalies.

(A) what the published D2 permutations act on, and whether they are physically the D2
    symmetry of the kept edge set (index -> point pairs compared by distance).
(B) the angular-velocity list printed by the CERTIFICATE vs the list written in
    STRESS-OBSTRUCTION.md: which is used, does it sum to 0, and where are the
    cap-active gaps?
"""
import json
import sys
from pathlib import Path
import mpmath as mp

LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\lead')
HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'evidence'
sys.path.insert(0, str(LEAD))
from root_integer_certificate import I, Q, S

mp.mp.dps = 60
log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

cert = json.loads((LEAD / 'root-integer-certificate.json').read_text())
X = [I(Q(a)*S, Q(b)*S, True) for a, b in cert['box_dyadic']]
z_i, c_i, r_i = X
s_i = (1 - r_i*r_i).sqrt(); a_i = (s_i + z_i)/2
t_i = r_i + (r_i*r_i - z_i*z_i).sqrt()
b_i = r_i + (r_i*r_i - (a_i - z_i)**2).sqrt()
d_i = 1 - (r_i*r_i - c_i*c_i).sqrt()
def mf(ivl):
    fr = Q(ivl.lo + ivl.hi, 2*S); return mp.mpf(fr.numerator)/fr.denominator

C = [(sx*a_i, sy*b_i) for sx in (-1, 1) for sy in (-1, 1)] + \
    [(sx*c_i, sy*d_i) for sx in (-1, 1) for sy in (-1, 1)] + \
    [(-s_i, I(0)), (s_i, I(0)), (z_i, I(0)), (-z_i, I(0)), (I(0), -t_i), (I(0), t_i)]
v1 = (1 + a_i*a_i + b_i*b_i - r_i*r_i)/2
v2 = (1 + c_i*c_i + d_i*d_i - r_i*r_i)/2
det = a_i*d_i - b_i*c_i
px_i = (v1*d_i - v2*b_i)/det
py_i = (a_i*v2 - c_i*v1)/det
anc = [(s_i, r_i), (px_i, py_i), (I(0), I(1)), (-px_i, py_i), (-s_i, r_i),
       (-s_i, -r_i), (-px_i, -py_i), (I(0), I(-1)), (px_i, -py_i), (s_i, -r_i)]

bary = json.loads((LEAD / 'stress-barycentric-result.json').read_text())
sym = json.loads((LEAD / 'stress-symmetry-control.json').read_text())
perms = sym['symmetry_permutations_weights']
P('=' * 78)
P('(A) the point attached to every kept index (rebuilt exactly as the script does)')
pos = {k: p for k, p in enumerate(anc)}
pos.update({10 + k: p for k, p in enumerate(C)})
faces = bary['faces']
P('   face-vertex indices are 10+i for centre i; the 6 kept faces are %s'
  % [i for i in range(14) if i not in (1, 4, 7, 10, 12, 13)])
kept_faces = [i for i in range(14) if i not in (1, 4, 7, 10, 12, 13)]
for i in kept_faces:
    P('      face %d ids %s' % (i, faces[i]['ids']))
kept_edges = []
idx = 14
for k, a in enumerate(bary['anchors']):
    for i in a['owners']:
        if idx in [i for i in range(14) if i not in (1, 4, 7, 10, 12, 13)] + [14+j for j in range(20)]:
            kept_edges.append((idx, k, 10 + i))
        idx += 1
P('   edge index -> (anchor, centre) pairs (lead variable index -> pair):')
for e, k, ci in kept_edges:
    P('      var %2d: anchor %d %s  centre %d %s' % (e, k, tuple(round(mf(q), 6) for q in anc[k]),
                                                    ci - 10, tuple(round(mf(q), 6) for q in C[ci - 10])))

P('')
P('(B) are the published permutations the physical D2 action on these pairs?')
def d2_of_point_map():
    return {'id': (1, 1), 'Sx': (-1, 1), 'Sy': (1, -1), 'C2': (-1, -1)}

# variable index -> pair of points (anchor, centre) for kept faces and edges
var_of = {}
for i in kept_faces:
    for ci in faces[i]['ids']:
        var_of.setdefault(i, None)
varpt = {}
for i in kept_faces:
    varpt[i] = None                      # a face variable lives on 3 vertices; test its vertices
for e, k, ci in kept_edges:
    varpt[e] = (anc[k], C[ci - 10])

for pi, p in enumerate(perms):
    best = None
    for nm, (ex, ey) in d2_of_point_map().items():
        ok = 0; tot = 0
        for e, (pa, pc) in ((e, v) for e, v in varpt.items() if v is not None):
            e2 = p[e]
            if e2 >= 34:
                continue
            tot += 1
            if e2 in varpt:
                qa, qc = varpt[e2]
                ok_a = abs(mf(qa[0]) - ex*mf(pa[0])) < mp.mpf('1e-20') and abs(mf(qa[1]) - ey*mf(pa[1])) < mp.mpf('1e-20')
                ok_c = abs(mf(qc[0]) - ex*mf(pc[0])) < mp.mpf('1e-20') and abs(mf(qc[1]) - ey*mf(pc[1])) < mp.mpf('1e-20')
                ok += 1 if (ok_a and ok_c) else 0
        if best is None or ok > best[1]:
            best = (nm, ok, tot)
    P('   perm %d: closest D2 map %s : %d/%d edge variables covariant' % (pi, best[0], best[1], best[2]))
    # also report the images of the first few kept edges
    P('      images of kept edge variables: %s'
      % [(e, p[e]) for e, (_a, _c) in ((e, v) for e, v in varpt.items() if v is not None)][:8])

P('')
P('=' * 78)
P('(C) angular velocities: certificate JSON vs the document list')
outcert = json.loads((LEAD / 'stress-obstruction-certificate.json').read_text())
ang = outcert['rational_anchor_angular_velocities']
angf = [mp.mpf(a) for a in ang]
P('   certificate list  : %s' % ang)
P('   sum(certificate)  = %s' % mp.nstr(sum(angf), 10))
doc = [mp.mpf(0), mp.mpf(-1)/4, mp.mpf(-2)/3, mp.mpf(-13)/12, mp.mpf(-4)/3,
       mp.mpf(-4)/3, mp.mpf(-13)/12, mp.mpf(-2)/3, mp.mpf(-1)/4, mp.mpf(0)]
P('   document list     : %s' % [mp.nstr(x, 6) for x in doc])
P('   sum(document)     = %s' % mp.nstr(sum(doc), 10))
P('   identical: %s' % (angf == doc))

ang_m = [mp.atan2(mf(y), mf(x)) for x, y in anc]
gaps = [(ang_m[(k+1) % 10] - ang_m[k]) % (2*mp.pi) for k in range(10)]
rp = mf(r_i); Lstar = 2*mp.asin(rp)
P('   L* = %s deg' % mp.nstr(mp.degrees(Lstar), 10))
P('   gap k, value, dg_k = v_{k+1}-v_k with the CERTIFICATE list:')
for k in range(10):
    d = angf[(k+1) % 10] - angf[k]
    tag = 'CAP-ACTIVE' if abs(gaps[k] - Lstar) < mp.mpf('1e-12') else ''
    P('      k=%d gap=%10.6f dg=%9.6f  v_k=%9.6f %s' % (k, mp.degrees(gaps[k]), d, angf[k], tag))
P('   cap-active gaps have dg = 0: %s'
  % [k for k in range(10) if abs(gaps[k] - Lstar) < mp.mpf('1e-12') and (angf[(k+1) % 10] - angf[k]) == 0])

(OUT / 'geo02_perms_velocity.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'geo02_perms_velocity.txt')
