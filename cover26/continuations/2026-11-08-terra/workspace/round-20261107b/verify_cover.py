"""Certify coverage at the same algebraic radius as the isolated root."""
from pathlib import Path
from fractions import Fraction as Q
from collections import defaultdict,Counter
import json,sys
from exact_model import build,anchor_data,boundary,circle_triangle,dot,norm,cross,sub,Poly,variable
from rational_interval import I,evaluator
from verify_root import certify,demand

HERE=Path(__file__).resolve().parent

def certify_cover():
    root,box=certify()
    C,G,_=build();r=variable(13);ev=evaluator(box)
    coordinates=[tuple(map(ev,c)) for c in C];radius=box[13]
    demand(radius.positive(),'positive algebraic covering radius')
    demand(len(C)==26 and len({(c[0].signature(),c[1].signature()) for c in C})==26,'26 distinct sites')
    demand(all((1-norm(c)).positive() for c in coordinates),'sites lie inside unit disk')
    faces=json.loads((HERE/'topology.json').read_text())['faces']
    demand(len(faces)==34 and len({tuple(sorted(f)) for f in faces})==34,'34 distinct faces')
    active=set(g.signature() for g in G[:8]);bndry=set(g.signature() for g in G[8:])
    anchors=[];tight=0;slack=[]
    for i in range(16):
        a,b=C[i],C[(i+1)%16]
        numerator,denominator,hi,hj=anchor_data(a,b,r)
        demand(boundary(a,b,r).signature() in bndry,'anchor unit-circle identity')
        # Polynomial identities certify exact equalities, which cannot be decided
        # by interval comparison around a tight contact.
        demand(2*dot(a,numerator)-hi*denominator==0,'anchor distance identity i')
        demand(2*dot(b,numerator)-hj*denominator==0,'anchor distance identity i+1')
        den=ev(denominator)
        demand(den.positive(),'anchor radical axes independent')
        anchors.append(tuple(ev(k)/den for k in numerator))
    for i,q in enumerate(anchors):
        nxt=anchors[(i+1)%16];prior=anchors[(i-1)%16];site=coordinates[i]
        demand(cross(q,nxt).positive() and dot(q,nxt).positive(),'anchor arc angle in (0,pi/2)')
        demand(cross(prior,site).positive() and cross(site,q).positive(),'site direction within own arc')
        expected=(1,1) if i<4 else (-1,1) if i<8 else (-1,-1) if i<12 else (1,-1)
        demand(all(q[k].positive() if expected[k]>0 else q[k].negative() for k in range(2)),
               'anchors wind exactly once')
    witnesses=[]
    for face in faces:
        demand(len(face)==3 and len(set(face))==3 and all(0<=j<26 for j in face),'face labels')
        a,b,c=[coordinates[j] for j in face]
        u,v=sub(b,a),sub(c,a);den=2*cross(u,v)
        demand(den.positive() or den.negative(),'nondegenerate center face')
        h,k=norm(b)-norm(a),norm(c)-norm(a)
        w=((h*v[1]-k*u[1])/den,(u[0]*k-v[0]*h)/den)
        demand((1-norm(w)).positive(),'witness in target disk')
        identity=circle_triangle(*(C[j] for j in face),r)
        if identity.signature() in active:
            # This equation is zero at the isolated root. The circumradius
            # identity and nonzero denominator give exact squared distance r^2.
            tight+=1
        else:
            demand((radius.square()-norm(sub(w,a))).positive(),'slack center face covered')
            demand((I(Q(232,1000)).square()-norm(sub(w,a))).positive(),'slack face radius below .232')
            slack.append(face)
        witnesses.append(w)
    demand(tight==30 and slack==[[2,3,19],[5,6,21],[10,11,23],[13,14,25]],'contact orbit classification')
    # Check the oriented chain independently of its geometric image. Degenerate
    # owner triangles at sites 0 and 8 are explicitly allowed.
    triangles=[]
    for i in range(16):
        triangles.extend([((i-1)%16,i,16+i),(i,16+i,16+(i+1)%16)])
    triangles.extend(tuple(16+j for j in face) for face in faces)
    incidence=defaultdict(list)
    for k,(a,b,c) in enumerate(triangles):
        for x,y in ((a,b),(b,c),(c,a)):
            incidence[tuple(sorted((x,y)))].append((k,1 if x<y else -1))
    demand(all(len(group) in (1,2) for group in incidence.values()),'edge multiplicity')
    orientation={0:1};todo=[0]
    while todo:
        k=todo.pop();a,b,c=triangles[k]
        for x,y in ((a,b),(b,c),(c,a)):
            group=incidence[tuple(sorted((x,y)))]
            if len(group)!=2:continue
            (i,di),(j,dj)=group;other=j if i==k else i;wanted=-orientation[k]*di*dj
            if other in orientation:demand(orientation[other]==wanted,'consistent chain orientation')
            else:orientation[other]=wanted;todo.append(other)
    demand(len(orientation)==66,'connected 66-face chain')
    directions=Counter()
    for k,(a,b,c) in enumerate(triangles):
        if orientation[k]<0:b,c=c,b
        directions.update([(a,b),(b,c),(c,a)])
    outer={tuple(sorted((i,(i+1)%16))) for i in range(16)}
    for edge,group in incidence.items():
        a,b=edge
        demand(len(group)==(1 if edge in outer else 2),'only boundary is anchor cycle')
        if edge not in outer:demand(directions[a,b]==directions[b,a]==1,'internal edge cancellation')
    for i in range(16):
        demand(directions[i,(i+1)%16]==1 and directions[(i+1)%16,i]==0,'positive anchor boundary')
    demand(len(incidence)==107 and 42-107+66==1,'Euler count')
    upper=Q('0.234700090400448239616790133776693')
    demand(radius.upper_fraction()<upper,'short rational upper bound')
    result={'passed':True,'exact_radius_definition':'unique real zero in root-proposal.json of the polynomial system in exact_model.py',
        'radius_decimal_upper':str(upper),'tight_center_faces':tight,'slack_center_faces':slack,
        'boundary_anchors':16,'boundary_contacts':32,'vertices':42,'edges':107,'oriented_faces':66,
        'degenerate_owner_faces_allowed':[0,8],
        'claim':'The 26 algebraic centers cover the closed unit disk at this same algebraic radius.',
        'global_optimality_proved':False}
    return result,coordinates,radius,witnesses,faces

if __name__=='__main__':
    result,C,r,witnesses,faces=certify_cover()
    if '--negative-control' in sys.argv:
        # The first face is a genuine nearest-site Voronoi vertex. For this
        # fixed algebraic configuration, shrinking its radius leaves it uncovered.
        witness=witnesses[0];smaller=r-I(Q(1,10**40))
        demand((1-norm(witness)).positive() and smaller.positive(),'negative-control domain')
        gaps=[norm(sub(witness,c))-smaller.square() for c in C]
        demand(all(gap.positive() for gap in gaps),'shrunk disks leave exact witness uncovered')
        print(json.dumps({'passed':True,'negative_control':'same centers, radius rho-10^-40 fails',
                          'uncovered_witness_face':faces[0]}))
    else:
        (HERE/'COVER-CERTIFICATE.json').write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps(result,indent=2))
