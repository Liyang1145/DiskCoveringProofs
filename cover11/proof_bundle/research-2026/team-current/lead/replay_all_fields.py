"""All 371 fields, exact rational Dirichlet Schur verification. No stored weights trusted."""
from certify_energy_cell import *
import hashlib,time
if __name__=='__main__':
 t=time.time();src=P/'cosine_dbm_local920.json';d=json.loads(src.read_text());checks=[]
 assert len(edges)==51 and len(set(edges))==51
 for num,f in enumerate(d['fields']):
  al=[sp.Rational(x) for x in f['alpha']];assert len(al)==51 and sum(al)==1 and min(al)>0
  LL=sp.zeros(31)
  for (v,w),a in zip(edges,al):LL[v,v]+=a;LL[w,w]+=a;LL[v,w]-=a;LL[w,v]-=a
  ff=LL[9:,9:];fa=LL[9:,:9];sol=ff.inv()*fa;assert ff*sol==fa
  M=LL[:9,:9]-LL[:9,9:]*sol;assert M==M.T and M*sp.ones(9,1)==sp.zeros(9,1)
  expected=[(i,j,str(F(-M[i,j]))) for i in range(9) for j in range(i+1,9)]
  assert [(i,j,str(F(w))) for i,j,w in f['weights']]==expected;assert all(F(w)>=0 for i,j,w in expected)
  checks.append(f['name'])
  if num%20==0:print(num,time.time()-t,flush=True)
 out={'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'verified_fields':len(checks),'field_names':checks,'seconds':time.time()-t,'scope':'exact Schur of all positive normalized51edge stresses'};(P/'all_fields_replay.json').write_text(json.dumps(out,indent=2));print('complete',len(checks),time.time()-t)
