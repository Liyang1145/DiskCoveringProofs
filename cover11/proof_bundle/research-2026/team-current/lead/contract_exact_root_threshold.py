"""Contract the SAME C891 root box and prove R* below the tree rational T.
Existence/uniqueness is C891. Iteration preserves inclusion of that known root.
Numerical inverse merely proposes one exact dyadic preconditioner.
"""
import json,time
from fractions import Fraction as F
import repair_tc_krawczyk as k
from mpmath import mp,iv
import numpy as np
mp.dps=90;iv.dps=70
P=k.P
cert=json.loads((P/'repaired_tc_krawczyk.json').read_text())['certificate']
c=[iv.mpf(float.fromhex(s)) for s in cert['center_hex']]
rad=iv.mpf(float.fromhex(cert['radius_hex']))
X=[v+iv.mpf([-k.hi(rad),k.hi(rad)]) for v in c]
f0,_=k.system(c,True)
_,jm=k.system([mp.mpf(float.fromhex(s)) for s in cert['center_hex']])
Y=iv.matrix(np.linalg.inv(np.array(jm,dtype=float)).tolist())
trace=[];start=time.time()
for it in range(6):
 # Fixed c may be OUTSIDE contracted X. MVT needs the convex hull(c,X),
 # not merely X. This is essential even though it limits asymptotic width.
 hull=[iv.mpf([min(k.lo(a),k.lo(b)),max(k.hi(a),k.hi(b))]) for a,b in zip(c,X)]
 _,jx=k.system(hull,True)
 E=iv.eye(12)-Y*iv.matrix(jx)
 shift=-Y*iv.matrix(f0)+E*iv.matrix([X[j]-c[j] for j in range(12)])
 K=[c[i]+shift[i] for i in range(12)]
 new=[]
 for a,b in zip(X,K):
  lo=max(k.lo(a),k.lo(b));hi=min(k.hi(a),k.hi(b));assert lo<=hi
  new.append(iv.mpf([lo,hi]))
 X=new
 trace.append({'iteration':it+1,'radius':[str(k.lo(X[6])),str(k.hi(X[6]))],'max_width':str(max(k.hi(x)-k.lo(x) for x in X))})
 print(trace[-1],flush=True)
T=iv.mpf(3799838531198387090485182)/10**25
assert X[6].b<T.a
assert X[6].b<(iv.mpf(19)/50).a
# Exact rational endpoint output, independent of decimal serialization.
def frac(m):
 sign,man,exp,bc=m._mpf_
 return F((-1 if sign else 1)*man)*(F(2)**exp)
out={'scope':'same unique C891 root; inclusion-preserving interval fixed-point contraction, not a different numeric root','initial_center_hex':cert['center_hex'],'initial_radius_hex':cert['radius_hex'],'T':'3799838531198387090485182/10000000000000000000000000','R_exact_rational_enclosure':[str(frac(k.lo(X[6]))),str(frac(k.hi(X[6])))],'gap_T_minus_R_lower':str(k.lo(T-X[6])),'Rstar_lt_T':True,'trace':trace,'seconds':time.time()-start}
(P/'exact_root_threshold.json').write_text(json.dumps(out,indent=2),encoding='utf8')
print('Rstar<T proved; gap lower',out['gap_T_minus_R_lower'],flush=True)
