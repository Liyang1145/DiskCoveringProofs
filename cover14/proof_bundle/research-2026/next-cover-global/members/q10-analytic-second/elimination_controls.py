"""Bounded calibration only; analytic theorem is in REPORT.md.
No imports of lead executable helpers. Reads frozen JSON coordinates/catalogue.
"""
import json, math
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
P=Path(__file__).resolve().parent
LEAD=P.parent.parent/'lead'

def sub(a,b): return (a[0]-b[0],a[1]-b[1])
def add(a,b): return (a[0]+b[0],a[1]+b[1])
def scale(a,t): return (a[0]*t,a[1]*t)
def norm2(a): return a[0]*a[0]+a[1]*a[1]
def triple(a,b,z,r,tol=0):
    A,B,C=norm2(sub(a,b)),norm2(sub(a,z)),norm2(sub(b,z))
    M=max(A,B,C)
    if M>4*r*r+tol:return False
    if 2*M>=A+B+C:return True
    u,v=sub(b,a),sub(z,a); cross=u[0]*v[1]-u[1]*v[0]
    return A*B*C<=4*r*r*cross*cross+tol

def circles(a,b,r):
    v=sub(b,a);d=math.sqrt(norm2(v))
    if d>2*r:return []
    if d==0:return [(a,2*r)]
    m=scale(add(a,b),.5)
    if d==2*r:return [(m,r)]
    w=scale((-v[1],v[0]),math.sqrt(max(0,r*r-d*d/4))/d)
    return [(a,2*r),(b,2*r),(add(m,w),r),(sub(m,w),r)]

def circle_intersections(c1,c2):
    a,R=c1;b,S=c2;v=sub(b,a);d=math.sqrt(norm2(v))
    if d==0 or d>R+S or d<abs(R-S):return []
    x=(d*d+R*R-S*S)/(2*d)
    h=math.sqrt(max(0,R*R-x*x));m=add(a,scale(v,x/d))
    w=scale((-v[1],v[0]),h/d)
    return [add(m,w),sub(m,w)]

def finite_test(pairs,r,tol=0,disks=()):
    cs=list(disks)
    for a,b in pairs:
        if norm2(sub(a,b))>4*r*r:return {'nonempty':False,'reason':'endpoint_distance'}
        cs.extend(circles(a,b,r))
    candidates=[(a[0]+R,a[1]) for a,R in cs]
    for c1,c2 in combinations(cs,2):candidates.extend(circle_intersections(c1,c2))
    passing=[p for p in candidates if all(triple(a,b,p,r,tol) for a,b in pairs) and all(norm2(sub(p,a))<=R*R+tol for a,R in disks)]
    return {'nonempty':bool(passing),'circle_count':len(cs),'candidate_count':len(candidates),'passing_count':len(passing),'first':passing[0] if passing else None}

# Exact rational controls distinguish pairwise edge constraints from triple constraints.
exact=[
 ('coincident',((F(0),F(0)),)*3,F(1),True),
 ('collinear_diameter',((F(-1),F(0)),(F(1),F(0)),(F(0),F(0))),F(1),True),
 ('right_triangle',((F(0),F(0)),(F(1),F(0)),(F(0),F(1))),F(1),True),
 ('acute_pairwise_not_enough',((F(-9,10),F(0)),(F(9,10),F(0)),(F(0),F(8,5))),F(1),False),
 ('obtuse',((F(-1),F(0)),(F(1),F(0)),(F(0),F(1,10))),F(1),True),
 ('duplicate_but_too_far',((F(0),F(0)),(F(0),F(0)),(F(3),F(0))),F(1),False)]
controls=[]
for name,pts,r,expected in exact:
    actual=triple(*pts,r);assert actual==expected
    controls.append({'name':name,'actual':actual,'expected':expected,'arithmetic':'Fraction'})

# Finite-intersection calibration: identical circles, tangency, empty,
# nondegenerate endpoint lenses, and singleton endpoint lens.
examples=[
 ('one_disk',[((0.,0.),(0.,0.))],True),
 ('tangent_disks',[((0.,0.),(0.,0.)),((4.,0.),(4.,0.))],True),
 ('empty_disks',[((0.,0.),(0.,0.)),((4.1,0.),(4.1,0.))],False),
 ('single_endpoint_lens',[((-1.,0.),(1.,0.))],True),
 ('two_nondegenerate_lenses',[((-.5,0.),(.5,0.)),((0.,-.5),(0.,.5))],True)]
for name,pairs,expected in examples:
    result=finite_test(pairs,1.,1e-12);assert result['nonempty']==expected
    controls.append({'name':name,'expected':expected,**result,'arithmetic':'float, tol=1e-12'})

G=json.loads((LEAD/'k10-catalogue-corrected.json').read_text())['10/4'][879]['faces']
pairs10=[tuple(v for v in f if v!=10) for f in G if 10 in f]
pairs12=[tuple(v for v in f if v!=12) for f in G if 12 in f]
retained=[f for f in G if 10 not in f and 12 not in f]
assert all(not(10 in f and 12 in f) for f in G)
assert pairs10==[(0,1),(0,9),(1,2),(2,11),(9,13),(11,13)]
assert pairs12==[(4,5),(4,11),(5,6),(6,7),(7,13),(11,13)]
assert retained==[[2,3,11],[3,4,11],[7,8,13],[8,9,13]]
D=json.loads((LEAD/'improved-upper-test.json').read_text())
old=[[float(F(x)) for x in p] for p in D['centers']]
match=json.loads((LEAD/'candidate-catalogue-match.json').read_text())['runs'][2]['exact_matches'][0]
C={int(new):old[int(prior)] for prior,new in match.items()}
r=.33173203427623414
candidate={}
for h,pairs in [(10,pairs10),(12,pairs12)]:
    endpoint_pairs=[(C[a],C[b]) for a,b in pairs]
    candidate[str(h)]={'saved_hub_passes':all(triple(a,b,C[h],r,1e-13) for a,b in endpoint_pairs),'elimination':finite_test(endpoint_pairs,r,1e-13)}
    assert candidate[str(h)]['saved_hub_passes']
    assert candidate[str(h)]['elimination']['nonempty']
# Audit the exact one-eliminated-site-per-face transversal, then test its
# boundary-owner factors on the same saved candidate (floating only).
E={3,8,10,12}
assert all(len(set(f)&E)==1 for f in G)
anchor_data=json.loads((LEAD/'stress-barycentric-result.json').read_text())['anchors']
anchors={}
for a in anchor_data:
    owners={int(match[str(i)]) for i in a['owners']}
    idx=next(j for j in range(10) if owners=={j,(j+1)%10})
    th=float(a['theta']); anchors[idx]=(math.cos(th),math.sin(th))
for h in [3,8]:
    pairs=[tuple(v for v in f if v!=h) for f in G if h in f]
    endpoint_pairs=[(C[a],C[b]) for a,b in pairs]
    disks=[(anchors[h-1],r),(anchors[h],r)]
    candidate[str(h)]={'saved_site_passes':all(triple(a,b,C[h],r,1e-13) for a,b in endpoint_pairs) and all(norm2(sub(C[h],a))<=R*R+1e-13 for a,R in disks),'elimination':finite_test(endpoint_pairs,r,1e-13,disks)}
    assert candidate[str(h)]['saved_site_passes']
    assert candidate[str(h)]['elimination']['nonempty']
out={'status':'analytic theorem separately; finite exact and floating controls, no continuum certificate', 'controls':controls,'graph_pairs10':pairs10,'graph_pairs12':pairs12,'retained':retained,'candidate_calibration':candidate,'candidate_tolerance':1e-13}
(P/'controls.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'controls':len(controls),'candidate':candidate},indent=2))
