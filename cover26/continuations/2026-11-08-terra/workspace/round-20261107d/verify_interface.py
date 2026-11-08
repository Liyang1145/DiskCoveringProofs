"""Exact numerical and symbolic premises of the new unrestricted geometry bridge.

The continuous topology and angle arguments are supplied in PROOF.md.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import combinations
import json,sys
import sympy as sp

HERE=Path(__file__).resolve().parent

def demand(p,message):
    if not p:raise ValueError(message)

def constants(U):
    def atan_inv(q):
        low=sum((Q((-1)**j,(2*j+1)*q**(2*j+1)) for j in range(40)),Q(0))
        return low,low+Q(1,81*q**81)
    a,b=atan_inv(5),atan_inv(239)
    pl,pu=16*a[0]-4*b[1],16*a[1]-4*b[0]
    p0=Q(314159265358979323846,10**20);p1=p0+Q(1,10**20)
    demand(p0<pl<pu<p1,'Machin enclosure')
    demand(0<U<Q(1,4),'8 nonowners without external theorem')
    demand((p0/13)-(p0/13)**3/6>U,'at least 14 owner arcs')
    demand(U*U+4*U<1,'at least 11 central boundary vertices')
    demand(9*U*U+2*U<1,'at least 8 central nonowners')
    return {'U':str(U),'owner_count_range':[14,18],
        'central_boundary_vertices_at_least':11,'central_nonowner_vertices_at_least':8,
        'central_boundary_inequality_gap':str(1-U*U-4*U),
        'central_nonowner_inequality_gap':str(1-9*U*U-2*U),
        'interior_incident_original_boundary_faces_at_least':{str(b):22-b for b in range(14,19)}}

if '--negative-control' in sys.argv:
    try:constants(Q(1,4))
    except ValueError as exc:
        print(json.dumps({'passed':True,'negative_control':'out-of-scope threshold rejected','reason':str(exc)}))
        raise SystemExit(0)
    raise ValueError('false scope accepted')

result=constants(Q(234701,10**6))
ax,ay,bx,by,cx,cy,dx,dy,qx,qy,t,s,k=sp.symbols('ax ay bx by cx cy dx dy qx qy t s k')
a=sp.Matrix([ax,ay]);b=sp.Matrix([bx,by]);c=sp.Matrix([cx,cy]);d=sp.Matrix([dx,dy]);q=sp.Matrix([qx,qy])
norm=lambda z:z.dot(z)
circle=lambda z:norm(z)-2*q.dot(z)+k
pab=(1-t)*a+t*b;pcd=(1-s)*c+s*d
A=t*(1-t)*norm(a-b);C=s*(1-s)*norm(c-d)
identities={
    'edge-variance':(1-t)*norm(a)+t*norm(b)-norm(pab)-A,
    'empty-circle-crossing':(1-s)*circle(c)+s*circle(d)-(1-t)*circle(a)-t*circle(b)-C+A
         -(pcd-pab).dot(pcd+pab-2*q),
}
for name,p in identities.items():demand(sp.expand(p)==0,name)
eta,zeta,rho=sp.symbols('eta zeta rho',real=True)
left=sp.Matrix([rho*(sp.cos(eta)-sp.cos(zeta)),rho*(sp.sin(eta)-sp.sin(zeta))])
right=2*rho*sp.sin((eta-zeta)/2)*sp.Matrix([-sp.sin((eta+zeta)/2),sp.cos((eta+zeta)/2)])
for component in left-right:demand(sp.trigsimp(sp.expand_trig(component))==0,'equal-anchor midpoint direction')
result['universal_symbolic_identities']=[*identities,'equal-anchor midpoint direction']

# All subsets of the relevant boundary cycles are checked, as a finite control
# of the separate written counting argument. This is not a sampling proof of geometry.
rows=[]
for b in range(14,19):
    mask_limit=(1<<b)-1;mins={j:b for j in range(11,b+1)};checked=0
    for mask in range(1<<b):
        count=mask.bit_count()
        if count<11:continue
        shifted=((mask<<1)|(mask>>(b-1)))&mask_limit
        adjacent=(mask&shifted).bit_count()
        demand(adjacent>=2*count-b,'boundary subset adjacency')
        mins[count]=min(mins[count],adjacent);checked+=1
    demand(mins[11]==22-b,'sharp finite subset minimum')
    rows.append({'b':b,'subsets_checked':checked,'minimum_original_edges_by_subset_size':mins})
result['finite_subset_controls']=rows

# New algebraic candidate is used only to check incidence bookkeeping, not as
# a representative for arbitrary covers.
faces=json.loads((HERE.parent/'round-20261107b/topology.json').read_text())['faces']
b=16;corners=[0]*26;h=[0]*26;N=[0,0,0]
cycle={tuple(sorted((i,(i+1)%b))) for i in range(b)}
for face in faces:
    count=sum(tuple(sorted(edge)) in cycle for edge in combinations(face,2))
    demand(count<=2,'boundary edge class')
    N[count]+=1
    for vertex in face:corners[vertex]+=1;h[vertex]+=count
demand(N[1]+2*N[2]==b and sum(h)==3*b,'global boundary incidence identities')
demand(sum(corners)==3*(50-b) and sum(h[b:])>=22-b,'candidate incidence control')
result['candidate_incidence_control']={'corners':corners,'boundary_face_incidence':h,
    'group_counts_by_cycle_edge_count':N,'total_nonowner_incidence':sum(h[b:]),
    'scope':'finite bookkeeping control only'}
result.update({'passed':True,'new_global_radius_lower_bound':None,'native_frontier_payments':0,
    'written_continuous_geometry_required':True})
(HERE/'INTERFACE-CERTIFICATE.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
