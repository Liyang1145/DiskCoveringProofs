"""Repair C408 kernel: interval center residual, symmetric displacement, fixed exact dyadic Y.
Only certifies an isolated 12D root of the explicitly specified symmetric TC KKT system.
No full-geometry/local-min/global implication. Historical AD is reused; independent derivative audit pending.
"""
import sys,json,hashlib,time
from pathlib import Path
import numpy as np
from mpmath import mp,iv
P=Path(__file__).parent;H=Path('research-2026/session2/n11tc/py').resolve();sys.path.insert(0,str(H))
import tc_s33_kkt as old
mp.dps=65;iv.dps=55
D=old.Dual;NZ=7;N=12

def bundle(z,interval):
 B=old.BK2_IV() if interval else old.BK2();C=iv.mpf if interval else mp.mpf
 xd=[]
 for k in range(NZ):
  inner=D(z[k],[C(int(j==k)) for j in range(NZ)])
  outer=[D(C(int(i==k)),[C(0) for j in range(NZ)]) for i in range(NZ)]
  xd.append(D(inner,outer))
 ff=old.K32.res5(xd[:4],xd[4],xd[5],xd[6],B)
 return [v.v.v for v in ff],[[v.v.d[i] for i in range(NZ)] for v in ff],[[[v.d[i].d[j] for j in range(NZ)] for i in range(NZ)] for v in ff]

def system(u,interval=False):
 C=iv.mpf if interval else mp.mpf
 f,j,h=bundle(u[:7],interval);lam=u[7:]
 F=f+[C(int(i==6))-sum(lam[k]*j[k][i] for k in range(5)) for i in range(7)]
 J=[[C(0) for j in range(N)] for i in range(N)]
 for k in range(5):
  for i in range(7):J[k][i]=j[k][i];J[5+i][7+k]=-j[k][i]
 for i in range(7):
  for j1 in range(7):J[5+i][j1]=-sum(lam[k]*h[k][i][j1] for k in range(5))
 return F,J

def lo(v):return mp.mpf(v.a)
def hi(v):return mp.mpf(v.b)
def bounds(v):return [mp.nstr(lo(v),58),mp.nstr(hi(v),58)]
def norm(v):return max(abs(lo(v)),abs(hi(v)))

def certify(uc,rad):
 # uc and rad are exact dyadic floats; no rounded decimal box endpoints.
 c=[iv.mpf(float(x)) for x in uc];d=iv.mpf(float(rad));Dlt=[iv.mpf([-float(rad),float(rad)]) for _ in uc];X=[c[i]+Dlt[i] for i in range(N)]
 f0,_=system(c,True);_,JX=system(X,True)
 _,Jmid=system([mp.mpf(float(x)) for x in uc]);Yf=np.linalg.inv(np.array(Jmid,dtype=float));Y=[[iv.mpf(float(v)) for v in row] for row in Yf]
 E=[[iv.mpf(int(i==j))-sum(Y[i][k]*JX[k][j] for k in range(N)) for j in range(N)] for i in range(N)]
 Q=max(hi(sum((abs(v) for v in row),iv.mpf(0))) for row in E) # outward row sums; mp only extracts exact endpoints
 shifts=[-sum(Y[i][k]*f0[k] for k in range(N))+sum(E[i][j]*Dlt[j] for j in range(N)) for i in range(N)]
 ok=all(lo(v)>-mp.mpf(float(rad)) and hi(v)<mp.mpf(float(rad)) for v in shifts)
 return {'pass_inclusion':ok,'contraction_inf':mp.nstr(Q,40),'contraction_lt1':bool(Q<1),'radius_hex':float(rad).hex(),'center_hex':[float(v).hex() for v in uc],'F_center':list(map(bounds,f0)),'K_minus_center':list(map(bounds,shifts)),'radius_coordinate_enclosure':bounds(c[6]+shifts[6]),'max_K_shift':mp.nstr(max(norm(v) for v in shifts),40)}

if __name__=='__main__':
 t=time.time();z=[mp.mpf(v) for v in old.CORE.xC]+[mp.mpf(old.CORE.RSTAR)]
 _,J,_=bundle(z,False);lam=mp.lu_solve(mp.matrix(J)*mp.matrix(J).T,mp.matrix(J)*mp.matrix([0]*6+[1]));u=z+list(lam)
 trace=[]
 for it in range(5):
  f,j=system(u);err=max(map(abs,f));trace.append(mp.nstr(err,35));print('newton',it,mp.nstr(err,8),flush=True)
  if err<mp.mpf('1e-55'):break
  du=mp.lu_solve(mp.matrix(j),-mp.matrix(f));u=[u[i]+du[i] for i in range(N)]
 uc=list(map(float,u));res=certify(uc,1e-9);print('certificate',res['pass_inclusion'],res['contraction_inf'],flush=True)
 # Known outside lambda-shift box must NOT certify a root.
 wrong=uc.copy();wrong[7]+=.01;bad=certify(wrong,1e-9)
 assert not bad['pass_inclusion']
 out={'scope':'root existence/uniqueness of symmetric TC KKT only; AD independent audit pending','newton_trace':trace,'numeric_root':[mp.nstr(v,62) for v in u],'certificate':res,'negative_control':bad,'seconds':time.time()-t,'source_hashes':{str(q):hashlib.sha256(q.read_bytes()).hexdigest() for q in [Path(__file__),H/'tc_s33_kkt.py',H/'tc_s32_kraw.py']}}
 (P/'repaired_tc_krawczyk.json').write_text(json.dumps(out,indent=2));print('done',out['seconds'],flush=True)
