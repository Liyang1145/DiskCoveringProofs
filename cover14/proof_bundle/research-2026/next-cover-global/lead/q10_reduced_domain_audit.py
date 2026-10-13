"""Independent normalizedrational active-support enumeration of C1331/C1332 domain."""
from q11_split_basis_audit import inv
from fractions import Fraction as Q
from pathlib import Path
from itertools import combinations
import json,hashlib,time
P=Path(__file__).resolve().parent
if __name__=='__main__':
 start=time.time();src=P/'q10-reduced-metric-domain.json';a=json.loads(src.read_text());poly=a['polytope'];cuts=[]
 for ids in [[8,9,0,1],[3,4,5,6]]:cuts.append(([Q(i in ids)for i in range(10)],Q(5,24)))
 for ids in [[0,1,2],[2,3,4],[5,6,7],[7,8,9]]:cuts.append(([-Q(i in ids)for i in range(10)],-Q(1,2)))
 assert poly['equality']==[['1']*10,['10','0','-1']];cs=poly['inequalities'];assert len(cs)==16
 for j,(n,r,_)in enumerate(cs[:10]):assert list(map(Q,n))==[Q(i==j)for i in range(10)]and list(map(Q,r))==[Q(0)]*3
 for (n,r,_),(nn,rr)in zip(cs[10:],cuts):assert list(map(Q,n))==nn and list(map(Q,r))==[10*rr,Q(0),-rr]
 V=set();bases=0
 for k in range(1,8):
  for supp in combinations(range(10),k):
   for active in combinations(range(6),k-1):
    M=[[Q(1)]*k]+[[cuts[c][0][j]for j in supp]for c in active];MI=inv(M)
    if MI is None:continue
    bases+=1;bb=[Q(1)]+[cuts[c][1]for c in active];w=[sum(MI[i][j]*bb[j]for j in range(k))for i in range(k)]
    if min(w)<0:continue
    v=[Q(0)]*10
    for j,x in zip(supp,w):v[j]=x
    if all(sum(n[j]*v[j]for j in range(10))>=r for n,r in cuts):V.add(tuple(v))
 expected={tuple((10*x,Q(0),-x)for x in v)for v in V};actual={tuple(tuple(map(Q,t))for t in v)for v in poly['vertex_set']};assert expected==actual
 out={'status':'independent_normalized_rational_complete_vertex_enumeration','vertices':len(V),'nonsingular_bases':bases,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'seconds':time.time()-start,'normalized_vertices':[[str(x)for x in v]for v in sorted(V)],'completeness':'A vertex with k positivecoordinates requires k−1 independent activecuts beyond sum; sixcuts imply k<=7. Enumerated allsupports/allactivecuts.'};(P/'q10-reduced-domain-audit.json').write_text(json.dumps(out,indent=2));print('REDUCEDAUDIT',len(V),bases,time.time()-start)
