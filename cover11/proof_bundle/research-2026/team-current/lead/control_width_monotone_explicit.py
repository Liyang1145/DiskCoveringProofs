"""Independent explicit derivative certificate, no AD helper."""
import heapq,json,time,math,hashlib
from interval_joint_patch import I,iv,acos,asin,lf,uf,g,P,z,R
start=time.time();heap=[];count=0;uid=0;closed={'illegal':0,'positive':0};minimum=math.inf
rd=(lf(I('.379')),uf(I('.37999')));dom=[rd,(lf(acos(I('.38'))/2),1),(lf(g),uf(2*asin(I('.38'))))]
def add(b,j):
 global count,uid,minimum
 count+=1;r,bb,w=[I(l,h)for l,h in b];x0=2*bb-acos(r);X=r*iv.sin(x0);D=1-r*iv.cos(x0)
 if X.b<0:closed['illegal']+=1;return
 W=2*iv.atan2(I(max(I(0).a,X.a),X.b),D)
 if w.a>W.b:closed['illegal']+=1;return
 p=D*iv.cos(w)+X*iv.sin(w);x=X*iv.cos(w)-D*iv.sin(w);cn=D*D+X*X
 qa=x*x+(1-p)**2;qb=1+cn-2*p;q=I(max(qa.a,qb.a),min(qa.b,qb.b))
 if q.a>0:
  mu,h,d,l=(z[1],z[112],z[34],z[96])if j==0 else(z[3],z[115],z[39],z[101])
  derivative=I('.5')-mu-p/2+(mu+h)*(cn-p)/q+2*d*x/R**2+l*x/(R*iv.sqrt(q))
  if derivative.a>0:closed['positive']+=1;minimum=min(minimum,lf(derivative));return
 k=max(range(3),key=lambda k:(b[k][1]-b[k][0])*[10,1,1][k]);priority=max((h-l)*s for (l,h),s in zip(b,[10,1,1]));heapq.heappush(heap,(-priority,uid,b,j,k));uid+=1
for j in [0,1]:add(dom,j)
while heap and count<8002:
 _,_,b,j,k=heapq.heappop(heap);l,h=b[k];m=(l+h)/2
 for ll,hh in [(l,m),(m,h)]:bb=b.copy();bb[k]=(ll,hh);add(bb,j)
out={'scope':'widthderivativepositive b<=1 explicitformula independentofAD','count':count,'live':len(heap),'closed':closed,'minimum':minimum,'seconds':time.time()-start,'domain':dom,'source_sha256':hashlib.sha256(__import__('pathlib').Path(__file__).read_bytes()).hexdigest()};(P/'width_monotone_explicit_control.json').write_text(json.dumps(out,indent=2));print(out)
