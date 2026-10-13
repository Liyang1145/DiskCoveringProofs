from pathlib import Path
import sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[1]/'lead'))
"""Directedinterval local-anchor to all14centers bridge viaexactbalancedflow slack."""
from root_integer_certificate import I,Q,S,P,json
import heapq,hashlib
root=json.loads((P/'root-integer-certificate.json').read_text());z,c,r=[I(int(Q(a)*S),int(Q(b)*S),True)for a,b in root['box_dyadic']];s=(1-r*r).sqrt();a=(s+z)/2;t=r+(r*r-z*z).sqrt();b=r+(r*r-(a-z)**2).sqrt();d=1-(r*r-c*c).sqrt();C=[(sx*a,sy*b)for sx in(-1,1)for sy in(-1,1)]+[(sx*c,sy*d)for sx in(-1,1)for sy in(-1,1)]+[(-s,I(0)),(s,I(0)),(z,I(0)),(-z,I(0)),(I(0),-t),(I(0),t)]
def norm(v):return sum((x*x for x in v),I(0))
def sq(v):return I(0,max(v.lo*v.lo,v.hi*v.hi)//S+1,True)if v.lo<=0<=v.hi else v*v
def upper(v):return Q(v.hi,S)
def lower(v):return Q(v.lo,S)
def absI(v):return I(max(abs(v.lo),abs(v.hi)),max(abs(v.lo),abs(v.hi)),True)
v1=(1+a*a+b*b-r*r)/2;v2=(1+c*c+d*d-r*r)/2;det=a*d-b*c;px=(v1*d-v2*b)/det;py=(a*v2-c*v1)/det;A=[(s,r),(px,py),(I(0),I(1)),(-px,py),(-s,r),(-s,-r),(-px,-py),(I(0),I(-1)),(px,-py),(s,-r)]
src=P/'dual-slack-symmetric-flow.json';flow=json.loads(src.read_text());base=json.loads((P/'fixed-anchor-flow-certificate.json').read_text())['runs'][0];D=base['incidence_matrix'];faces=base['faces'];owners=base['owners'];zz=[[Q(x)for x in v]for v in flow['flow_vectors']];nv=len(D[0]);nf=len(faces);expected=[]
for j,face in enumerate(faces):
 for v in face:
  dr=[0]*nv;dr[v]=1;dr[14+j]=-1;expected.append(dr)
for pair in owners:
 for v in pair:
  dr=[0]*nv;dr[v]=1;expected.append(dr)
assert nv==14+nf and D==expected and len(zz)==3*nf+2*len(A)
assert all(sum(Q(D[e][j])*zz[e][k]for e in range(len(zz)))==0 for j in range(nv)for k in range(2));W=[]
for face in faces:
 p,q,v=[C[i]for i in face];u=[q[j]-p[j]for j in range(2)];w=[v[j]-p[j]for j in range(2)];de=u[0]*w[1]-u[1]*w[0];aa=(norm(q)-norm(p))/2;bb=(norm(v)-norm(p))/2;W.append(((aa*w[1]-u[1]*bb)/de,(u[0]*bb-aa*w[0])/de))
pts=C+W;weights=[I(sum(x*x for x in v)).sqrt()if any(v)else I(0)for v in zz];N=sum(weights,I(0));g=[[-sum(zz[3*nf+2*j+h][k]for h in range(2))for k in range(2)]for j in range(10)];F0=sum((I(g[j][k])*A[j][k]for j in range(10)for k in range(2)),I(0));T=sum((absI(I(g[j][0])*(-A[j][1])+I(g[j][1])*A[j][0])for j in range(10)),I(0));G=sum((I(sum(x*x for x in gg)).sqrt()if any(gg)else I(0)for gg in g),I(0));import sys
epsilon=Q(sys.argv[1])if len(sys.argv)>1 else Q(1,10**6);Lmin=F0-T*epsilon-G*epsilon**2/2;U=Q('.33173203427623414');slack=I(U)*N-Lmin;E=2*U*I(upper(slack));alignment=I(0);adj=[[]for _ in range(nv+1)]
for e,dr in enumerate(D):
 if not any(zz[e]):continue
 u=dr.index(1);v=dr.index(-1)if -1 in dr else nv;anchor=(e-3*nf)//2 if v==nv else None;pp=[pts[u][k]-(pts[v][k]if v<nv else A[anchor][k])for k in range(2)];res=[pp[k]-r*I(zz[e][k])/weights[e]for k in range(2)];alignment+=weights[e]*sum((sq(x)for x in res),I(0));cost=upper(1/weights[e]);adj[u].append((v,cost));adj[v].append((u,cost))
dist=[None]*(nv+1);dist[nv]=Q(0);pending=[(Q(0),nv)]
while pending:
 dd,u=heapq.heappop(pending)
 if dd!=dist[u]:continue
 for v,cost in adj[u]:
  if dist[v]is None or dd+cost<dist[v]:dist[v]=dd+cost;heapq.heappush(pending,(dist[v],v))
assert all(x is not None for x in dist[:14]);R=max(dist[:14]);rlo=lower(Lmin/N);assert rlo>0;rhoerr=max(abs(rlo/upper(r)-1),abs(U/lower(r)-1));Eroot=E.sqrt()+(I(U)/r)*I(upper(alignment)).sqrt();diam=max(upper(norm([cc[k]-aa[k]for k in range(2)]).sqrt())for cc in C for aa in A);siteerror=I(epsilon+rhoerr*diam)+I(R).sqrt()*Eroot
# Gauge y(X+)=0: rotationangle<=2 siteerror/s_lower for sufficientlysmallerror.
assert upper(siteerror)<lower(s)/4
rotation=2*siteerror/lower(s);maxsite=max(upper(norm(cc).sqrt())for cc in C);gaugederror=siteerror+rotation*maxsite;assert upper(gaugederror)<Q(4,10**5)
out={'status':'certified_anchor_cell_to_C1262_local_box','epsilon_radians':str(epsilon),'scope':'same literalface/ownerlabeling afterglobalrotation; all10referenceanchorangles differ<=epsilon; arbitraryfeasiblewitnesssystem r<=U','sources':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in [src,P/'root-integer-certificate.json',P/'fixed-anchor-flow-certificate.json']},'intervals':{name:v.dec()for name,v in [('N',N),('F0',F0),('tangential_L1',T),('slack_upper',I(upper(slack))),('alignment',alignment),('site_error',siteerror),('gauged_site_error',gaugederror)]},'path_resistance_upper':str(R),'radius_lower':str(rlo),'gauged_error_display':float(upper(gaugederror))};(HERE/'dual-comparison-2e6.json').write_text(json.dumps(out,indent=2));print('LOCAL BRIDGE',out['gauged_error_display'],'eps',epsilon)
