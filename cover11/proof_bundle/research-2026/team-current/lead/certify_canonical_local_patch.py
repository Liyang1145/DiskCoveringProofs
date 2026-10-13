"""Translate adaptive raw-ball certificate into exact rational y-polytope.
C891 root source recurrence; no decimal radius/angle is used as exact candidate.
"""
from simplex_tree_pilot import *
cert=json.loads((P/'repaired_tc_krawczyk.json').read_text())['certificate']
rr=F(float.fromhex(cert['radius_hex']))
u=[I(F(float.fromhex(x)))+iv.mpf([-hi(I(rr)),hi(I(rr))]) for x in cert['center_hex']];z=u[:7]
a=[z[0],z[1],z[2],z[3],iv.pi-2*sum(z[:4]),z[3],z[2],z[1],z[0]]
th=[iv.mpf(0) for i in range(9)]
for k in range(5,9):th[k]=th[k-1]+a[k-1]+a[k]
for k in range(3,-1,-1):th[k]=th[k+1]-a[k]-a[k+1]
raw=[th[k]+a[k] for k in range(9)]
# Increasing unwrapped raw tie angles, root center-angle theta4=0 unrelated to gauge.
assert all(raw[k+1]-raw[k]>0 for k in range(8))
can=[iv.mpf(0)]+[raw[(i+2)%9]-raw[2]+(2*iv.pi if i>=7 else 0) for i in range(1,9)]
width=[can[i+1]-can[i] for i in range(8)]+[2*iv.pi-can[8]]
assert all(w>0 and w<L for w in width)
y0=[(L-w)/D for w in width]
center=[F(round(float((lo(x)+hi(x))/2)*10**12),10**12) for x in y0[:8]];center.append(1-sum(center))
eps=F(1,50000)
# Cell: independent y0..7 within eps of center, y8=1-sum0..7. Entire cube must lie in P.
assert all(I(center[i]-eps)>0 for i in range(8)) and I(center[8]-8*eps)>0
# Direct linear map x_raw[k]=delta_can[(k-2)%9]-delta_can[6]. x_raw8=0.
# Canonical theta box from affine prefix ranges, root interval subtracted.
cy=[iv.mpf([lo(I(c-eps)),hi(I(c+eps))]) for c in center[:8]]
# evaluate canonical theta displacement directly: constants iL cancel vs root only numerically enclosed, harmless.
delta=[iv.mpf(0)]+[i*L-D*sum(cy[:i])-can[i] for i in range(1,9)]
h=[delta[(k-2)%9]-delta[6] for k in range(8)]
# interval square norm encloses every point in full cube; no vertex sampling.
# Explicit componentwise outward upper, with squaring performed in interval arithmetic.
norm2safe=sum(iv.mpf(max(abs(lo(v)),abs(hi(v))))**2 for v in h)
rho=F(431,1000000)
# Fallback universal norm bound 4*canonical displacement if direct interval dependence loses too much.
can2=sum(iv.mpf(max(abs(lo(v)),abs(hi(v))))**2 for v in delta)
assert min(hi(norm2safe),hi(16*can2)) < lo(I(rho)**2)
# Exact-root belongs to the rational patch (including dependent9thcoordinate bysum).
assert all(I(center[i]-eps)<y0[i] and y0[i]<I(center[i]+eps) for i in range(8))
# Incidence isomorphism for source raw carrying graph to canonical fullgraph (orientations arbitrary for scalar weights).
rawF=[[2,9,10],[6,9,10]]+[[k,(k+1)%9,9 if 2<=k<=5 else 10] for k in [1,2,3,4,5,6,8]]
shift=lambda s: (s-2)%9 if s<9 else s
canfaces={tuple(sorted(f)) for f in faces};assert len(rawF)==9 and all(tuple(sorted(map(shift,f))) in canfaces for f in rawF)
# Check all18 anchor-site edges independently of width naming. Raw anchor k is tied to raw sites k,k+1;
# shifting both produces canonical site s with anchors s,s-1, exactly simplex_tree_pilot edges.
raw_endpoint_pairs={(shift(s),shift(k)) for k in range(9) for s in [k,(k+1)%9]}
canonical_endpoint_pairs={(s,j) for s in range(9) for j in [s,(s-1)%9]}
assert raw_endpoint_pairs==canonical_endpoint_pairs
# Thus canonical site s owns anchor gap s-1, whereas width[i] is forward anchor gap i;
# P constrains all9 gaps identically, so this intentional index offset makes no change to P.
out={'status':'proved-interval containment conditional on adaptive ball lemma/constants','scope':'rational8cube in y0..7 with y8=1-sum, subset P and contains exact candidate','center_y':[str(x) for x in center],'halfwidth_independent8':str(eps),'raw_ball_radius':str(rho),'norm2_direct_upper':str(hi(norm2safe)),'norm2_via_operator4_upper':str(hi(16*can2)),'rho2_lower':str(lo(I(rho)**2)),'candidate_y_intervals':[[str(lo(x)),str(hi(x))] for x in y0],'canonical_root_angles':[[str(lo(x)),str(hi(x))] for x in can],'rotation_map':'raw h_k=delta_can[(k-2)%9]-delta_can6,k0..7;raw8=0','conclusion':'whole rational cube has V²>=R*² using adaptive_stress_ball_certificate.json and ADAPTIVE-STRESS-FINITE-REMAINDER.md'}
(P/'canonical_local_patch_certificate.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items() if k not in ['candidate_y_intervals','canonical_root_angles']})
