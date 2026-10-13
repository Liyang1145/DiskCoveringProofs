"""Read-only all-leaf replay, no numerical LP/solver. Recompute each intercept from exact slopes and current cell, never trust serialized decimal endpoints."""
from cosine_dbm_pilot import *
from certify_cosine_envelope_cell import intercept as ci
import hashlib,time

def replay(n,fields):
 db=[[F(x) for x in r] for r in n['db']]
 if n.get('patch'):
  pp=known_patch(db);assert pp is not None;return 'patch'
 cc=n['certificate'];beta=list(map(F,cc['beta']));assert len(beta)<=len(fields) and min(beta)>=0 and sum(beta)==1
 c=[iv.mpf(0) for _ in range(9)];f0=iv.mpf(0)
 assert len(cc['minorants'])==36
 for k,(i,j) in enumerate(pairs):
  rec=cc['minorants'][k];assert rec['pair']==[i,j]
  W=sum(beta[t]*2*F(fields[t]['weights'][k][2]) for t in range(len(beta)));assert W==F(rec['weight']) and W>=0
  a=lo((i-j)*L+D*I(-db[j][i]));b=hi((i-j)*L+D*I(db[i][j]));lines=rec['lines'];assert sum(F(z['gamma']) for z in lines)==1
  for z in lines:
   g,s=F(z['gamma']),F(z['slope']);assert g>=0
   v=ci(a,b,s);f0+=I(W*g)*(I(s)*(i-j)*L+iv.mpf(v))
   for t in range(i,j):c[t]+=I(W*g*s)*D
 A,bb=domain_rows(db);lam=list(map(F,cc['lambda']));assert len(lam)==len(A) and min(lam)>=0
 residual=[c[k]+I(sum(lam[j]*A[j][k] for j in range(len(A)))) for k in range(9)]
 lb=lo(f0-I(sum(x*y for x,y in zip(lam,bb)))+iv.mpf(min(lo(v) for v in residual)))
 target=F(cc.get('target','19/50'));assert iv.mpf(lb)>I(target)**2
 assert target>=F(3799838531198387090485182,10**25)
 return 'energy'
if __name__=='__main__':
 start=time.time();src=P/'cosine_dbm_local920.json';d=json.loads(src.read_text());nodes=d['nodes'];fields=d['fields'];assert [[F(x) for x in r] for r in nodes[0]['db']]==rootdbm();seen={0};count={'patch':0,'energy':0,'split':0}
 for idx,n in enumerate(nodes):
  assert idx==n['id'];db=[[F(x) for x in r] for r in n['db']]
  if n['status']=='split':
   mid,a,b=branches(db,n['pair']);assert str(mid)==n['midpoint'] and len(n['children'])==2
   for ch,child in zip(n['children'],[a,b]):assert ch not in seen and [[F(x) for x in r] for r in nodes[ch]['db']]==child;seen.add(ch)
   count['split']+=1
  else:
   assert n['status']=='certified';count[replay(n,fields)]+=1
  if idx%200==0:print(idx,count,flush=True)
 assert seen==set(range(len(nodes)))
 out={'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'counts':count,'seconds':time.time()-start,'scope':'all cells replayed, field weights still require Schur evidence'};(P/'closed_dbm_replay.json').write_text(json.dumps(out,indent=2));print(out)
