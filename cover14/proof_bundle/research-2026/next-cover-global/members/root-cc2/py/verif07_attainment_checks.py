"""root-cc2: representation check of lead/root_cover_check.py + ROOT-ATTAINMENT.md.

Uses the LEAD's own integer interval kernel (imported) so this is a check of their
recorded objects, not a new proof chain.

Checks
------
(1) print both 14-site enumerations (lead order and my audit04 order) physically.
(2) translate the lead's index triples into physical coordinate triples and compare
    with my independent enumeration: same physical triple sets?
(3) classify the 16 remaining triples into the four claimed shapes.
(4) boundary anchors: cyclic angles, every gap in (0,pi), every anchor inside its owner
    disk, and the exact contact identities of ROOT-ATTAINMENT.md.
"""
import json
import sys
from pathlib import Path
import mpmath as mp

HERE = Path(__file__).resolve().parent
LEAD = HERE.parents[2] / 'lead'
sys.path.insert(0, str(LEAD))
from root_integer_certificate import I, J, Q, S, iv

mp.mp.dps = 60
log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

def midf(ivl):
    """midpoint of the lead's interval as mpf"""
    fr = Q(ivl.lo + ivl.hi, 2*S)
    return mp.mpf(fr.numerator) / fr.denominator

def ex(ivl, n=8):
    """exact-ish decimal of an interval endpoint (as a rational string)"""
    return mp.nstr(mp.mpf(Q(ivl, S).numerator) / Q(ivl, S).denominator, n)

cert = json.loads((LEAD / 'root-integer-certificate.json').read_text())
ctrl = json.loads((LEAD / 'root-cover-controls.json').read_text())
X = [I(Q(a)*S, Q(b)*S, True) for a, b in cert['box_dyadic']]
z_i, c_i, r_i = X
s_i = (1 - r_i*r_i).sqrt(); a_i = (s_i + z_i)/2
t_i = r_i + (r_i*r_i - z_i*z_i).sqrt()
b_i = r_i + (r_i*r_i - (a_i - z_i)**2).sqrt()
d_i = 1 - (r_i*r_i - c_i*c_i).sqrt()

C_lead = [(sx*a_i, sy*b_i) for sx in (-1, 1) for sy in (-1, 1)] + \
         [(sx*c_i, sy*d_i) for sx in (-1, 1) for sy in (-1, 1)] + \
         [(s_i, I(0)), (-s_i, I(0)), (z_i, I(0)), (-z_i, I(0)), (I(0), t_i), (I(0), -t_i)]
C_mine = [(-a_i, -b_i), (-a_i, b_i), (a_i, -b_i), (a_i, b_i),
          (c_i, -d_i), (c_i, d_i), (-c_i, -d_i), (-c_i, d_i),
          (-s_i, I(0)), (s_i, I(0)), (z_i, I(0)), (-z_i, I(0)),
          (I(0), -t_i), (I(0), t_i)]

def key(p):
    return (mp.nstr(midf(p[0]), 12), mp.nstr(midf(p[1]), 12))

P('=' * 78)
P('(1) both enumerations, physical')
P('   lead index -> (x,y)   [root_cover_check.py order]')
for i, p in enumerate(C_lead):
    P('      %2d  (%s, %s)' % (i, mp.nstr(midf(p[0]), 16), mp.nstr(midf(p[1]), 16)))
P('   my index -> (x,y)     [audit04 order]')
for i, p in enumerate(C_mine):
    P('      %2d  (%s, %s)' % (i, mp.nstr(midf(p[0]), 16), mp.nstr(midf(p[1]), 16)))
P('   sites are the same 14 physical points: %s'
  % (sorted(key(p) for p in C_lead) == sorted(key(p) for p in C_mine)))

P('')
P('=' * 78)
P('(2) the 16 remaining triples as PHYSICAL triples (translated through the 14-site map)')
site_map = {key(C_lead[i]): key(C_mine[j]) for i in range(14) for j in range(14)
            if key(C_lead[i]) == key(C_mine[j])}
lead_tight, lead_slack = set(), set()
for e in ctrl['remaining_triples']:
    phys = tuple(sorted(site_map[key(C_lead[i])] for i in e['ids']))
    (lead_slack if e['slack_certified'] else lead_tight).add(phys)
P('   tight physical triples (%d):' % len(lead_tight))
for t in sorted(lead_tight):
    P('      %s' % str(t))
P('   slack physical triples (%d):' % len(lead_slack))
for t in sorted(lead_slack):
    P('      %s' % str(t))

# my independent classification, recomputed here from the lead's box coordinates
tight_mine, slack_mine = set(), set()
for ids in __import__('itertools').combinations(range(14), 3):
    p, q, v = C_mine[ids[0]], C_mine[ids[1]], C_mine[ids[2]]
    detv = I(2)*( (q[0]-p[0])*(v[1]-p[1]) - (q[1]-p[1])*(v[0]-p[0]) )
    if detv.lo <= 0 <= detv.hi:
        continue
    u = (q[0]*q[0]+q[1]*q[1]) - (p[0]*p[0]+p[1]*p[1])
    w = (v[0]*v[0]+v[1]*v[1]) - (p[0]*p[0]+p[1]*p[1])
    cx = (u*(v[1]-p[1]) - w*(q[1]-p[1]))/detv
    cy = ((q[0]-p[0])*w - (v[0]-p[0])*u)/detv
    if (cx*cx + cy*cy).lo > I(1).lo*S:
        continue
    rad = (cx-p[0])*(cx-p[0]) + (cy-p[1])*(cy-p[1])
    if any((((cx-C_mine[j][0])**2 + (cy-C_mine[j][1])**2) - rad).hi < 0
           for j in range(14) if j not in ids):
        continue
    (slack_mine if (rad - r_i*r_i).hi < 0 else tight_mine).add(tuple(sorted(key(C_mine[i]) for i in ids)))
P('   my recomputation from the same coordinates: %d tight, %d slack'
  % (len(tight_mine), len(slack_mine)))
P('   tight sets equal: %s' % (lead_tight == tight_mine))
P('   slack sets equal: %s' % (lead_slack == slack_mine))

P('')
P('=' * 78)
P('(3) shape classification of the 14 tight triples (my labels)')
def lab(k):
    if k in {key(C_mine[i]) for i in (0, 1, 2, 3)}: return 'A(a,b)'
    if k in {key(C_mine[i]) for i in (4, 5, 6, 7)}: return 'C(c,d)'
    if k in {key(C_mine[i]) for i in (8, 9)}: return 'X(+-s,0)'
    if k in {key(C_mine[i]) for i in (10, 11)}: return 'Z(+-z,0)'
    return 'T(0,+-t)'
shapes = {}
for t in lead_tight:
    shapes.setdefault(tuple(sorted(lab(x) for x in t)), []).append(t)
for sig, lst in sorted(shapes.items()):
    P('      %-28s x%d' % (str(sig), len(lst)))

P('')
P('=' * 78)
P('(4) boundary anchors (index-free checks on the lead\'s recorded objects)')
v1 = (1 + a_i*a_i + b_i*b_i - r_i*r_i)/2
v2 = (1 + c_i*c_i + d_i*d_i - r_i*r_i)/2
det = a_i*d_i - b_i*c_i
px_i = (v1*d_i - v2*b_i)/det
py_i = (a_i*v2 - c_i*v1)/det
anchors = [(s_i, r_i), (px_i, py_i), (I(0), I(1)), (-px_i, py_i), (-s_i, r_i),
           (-s_i, -r_i), (-px_i, -py_i), (I(0), I(-1)), (px_i, -py_i), (s_i, -r_i)]
angles = [mp.atan2(midf(y), midf(x)) for x, y in anchors]
owners = ctrl['anchor_owner_order']
bad = 0
for i in range(10):
    nxt = (angles[(i+1) % 10] - angles[i]) % (2*mp.pi)
    ok = 0 < nxt < mp.pi
    bad += 0 if ok else 1
    P('      anchor %2d (%9.6f, %9.6f)  angle %8.3f  gap %7.3f  in(0,pi): %s  owner %2d'
      % (i, midf(anchors[i][0]), midf(anchors[i][1]), mp.degrees(angles[i]),
         mp.degrees(nxt), ok, owners[i]))
P('   gaps violating (0,pi): %d ; sum of gaps = %s deg'
  % (bad, mp.nstr(mp.degrees(sum(((angles[(i+1) % 10] - angles[i]) % (2*mp.pi) for i in range(10)))), 12)))
def d2(p, q):
    return (p[0]-q[0])*(p[0]-q[0]) + (p[1]-q[1])*(p[1]-q[1])
r2 = r_i*r_i
nstrict = 0
for i in range(10):
    for lab_, pt in (('i', anchors[i]), ('i+1', anchors[(i+1) % 10])):
        dd = d2(pt, C_lead[owners[i]])
        if dd.hi < r2.lo:
            nstrict += 1
P('   anchor-in-owner-disk: all %d checks pass: %s ; strict (< r^2): %d'
  % (20, all(d2(pt, C_lead[owners[i]]).lo <= r2.hi for i in range(10)
             for pt in (anchors[i], anchors[(i+1) % 10])), nstrict))
P('   exact contact identities (squared distance - r^2 intervals):')
for lab_, pt, own in (('(s,r) vs X(s,0)', (s_i, r_i), C_lead[9]),
                      ('(s,r) vs A(a,b)', (s_i, r_i), C_lead[3]),
                      ('(0,1) vs C(c,d)', (I(0), I(1)), C_lead[7]),
                      ('p vs A', (px_i, py_i), C_lead[3]),
                      ('p vs C', (px_i, py_i), C_lead[5])):
    dd = d2(pt, own) - r2
    P('      %-16s [%s, %s]  contains 0: %s' % (lab_, ex(dd.lo), ex(dd.hi), dd.lo <= 0 <= dd.hi))

(HERE.parent / 'evidence' / 'verif07_attainment_checks.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written] evidence/verif07_attainment_checks.txt')
