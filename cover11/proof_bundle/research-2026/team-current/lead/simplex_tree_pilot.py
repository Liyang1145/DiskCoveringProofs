"""Bounded 127-node trial, exact y-tree + rational vector fields + interval LB.
No solver calls. Every unresolved leaf retained. NOT a global certificate.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import deque
import json
from mpmath import mp,iv
mp.dps=80;iv.dps=50
P=Path(__file__).resolve().parent
faces=[[9,k,k+1] for k in range(4)]+[[10,k,(k+1)%9] for k in range(4,9)]+[[9,10,0],[9,10,4]]
edges=[e for s in range(9) for e in [(9+s,s),(9+s,(s-1)%9)]]+[(9+s,20+j) for j,f in enumerate(faces) for s in f]
def I(q):
 q=F(q);return iv.mpf(q.numerator)/q.denominator
def lo(x):return mp.mpf(x.a)
def hi(x):return mp.mpf(x.b)
def balance(p):
 b=[[F(0),F(0)] for _ in range(31)]
 for (v,w),q in zip(edges,p):
  for k in range(2):b[v][k]+=q[k];b[w][k]-=q[k]
 return b

def repair(raw):
 p=[[F(round(float(v)*10**12),10**12) for v in row] for row in raw]
 assert len(p)==51
 b=balance(p);adj=[[] for _ in range(31)]
 for j,(v,w) in enumerate(edges):adj[v].append((w,j));adj[w].append((v,j))
 par={i:None for i in range(9)};queue=deque(range(9));order=[]
 while queue:
  v=queue.popleft();order.append(v)
  for w,j in adj[v]:
   if w not in par:par[w]=(v,j);queue.append(w)
 assert len(par)==31
 for v in reversed(order):
  if v<9:continue
  w,j=par[v];sgn=1 if edges[j][0]==v else -1
  for k in range(2):p[j][k]-=sgn*b[v][k];b[w][k]+=b[v][k];b[v][k]=0
 assert all(x==0 for row in balance(p)[9:] for x in row)
 norm=sum(iv.sqrt(sum(I(v)**2 for v in q)) for q in p)
 B=F(int(mp.ceil(hi(norm)*10**12))+1,10**12)
 assert I(B)>norm
 return [[v/B for v in q] for q in p]

def field(p,name):
 b=balance(p);assert all(x==0 for row in b[9:] for x in row)
 assert sum(iv.sqrt(sum(I(v)**2 for v in q)) for q in p)<=1
 return {'name':name,'forces':p,'loads':b[:9]}
L=2*iv.atan2(I(F(19,50)),iv.sqrt(1-I(F(19,50))**2));D=9*L-2*iv.pi
assert D>0

def angles(y):return [i*L-D*I(sum(y[:i])) for i in range(9)]
def lower(vertices,ff):
 th=[angles(v) for v in vertices];loads=ff['loads']
 vals=[sum(I(loads[i][0])*iv.cos(t[i])+I(loads[i][1])*iv.sin(t[i]) for i in range(9)) for t in th]
 penalty=iv.mpf(0)
 for i in range(9):
  a=min(lo(t[i]) for t in th);b=max(hi(t[i]) for t in th);arc=iv.mpf([a,b])
  val=I(loads[i][0])*iv.cos(arc)+I(loads[i][1])*iv.sin(arc)
  k=max(mp.mpf(0),-lo(val));width=iv.mpf(b)-iv.mpf(a)
  penalty+=iv.mpf(k)*width**2/8
 return iv.mpf(min(lo(v) for v in vals))-penalty

def split(v):
 pairs=[(sum((v[i][k]-v[j][k])**2 for k in range(9)),i,j) for i in range(9) for j in range(i+1,9)]
 length=max(x[0] for x in pairs);_,i,j=next(x for x in pairs if x[0]==length)
 mid=[(a+b)/2 for a,b in zip(v[i],v[j])]
 a=[r[:] for r in v];b=[r[:] for r in v];a[i]=mid;b[j]=mid
 return i,j,a,b

def main():
 c=json.loads((P/'uniform_sector_certificate.json').read_text());assert [tuple(e) for e in c['edges']]==edges
 fields=[field([[F(v) for v in row] for row in c['forces_rational']],'C911')]
 proposals=json.loads((P.parent/'r20-alternative/fixed_oracle_force_proposal.json').read_text())['points']
 for row in proposals:fields.append(field(repair(row['force_vectors_51']),row['name']))
 # Control: existing C913 coupled simplex must pass; radius point>=0 and force sign reversal must fail.
 t=F(19,50);patch=[[F(1-t,9)+(t if i==j else 0) for i in range(9)] for j in range(9)]
 assert lower(patch,fields[0])>I(F(19,50))
 reverse=field([[-x for x in q] for q in fields[0]['forces']],'reverse')
 assert lower(patch,reverse)<0
 root=[[F(i==j) for i in range(9)] for j in range(9)]
 nodes=[{'id':0,'vertices':root,'depth':0}];queue=deque([0]);processed=0
 while queue and processed<127:
  idx=queue.popleft();node=nodes[idx];v=node['vertices'];lbs=[lower(v,ff) for ff in fields];best=max(range(len(lbs)),key=lambda k:lo(lbs[k]));lb=lbs[best]
  node.update({'lower':str(lo(lb)),'field':best});processed+=1
  if lb>I(F(19,50)):node['status']='certified';continue
  if len(nodes)+2>255:node['status']='open';continue
  i,j,a,b=split(v);node.update({'status':'split','edge':[i,j],'children':[len(nodes),len(nodes)+1]})
  for vv in [a,b]:
   nxt=len(nodes);nodes.append({'id':nxt,'vertices':vv,'depth':node['depth']+1});queue.append(nxt)
 for n in nodes:
  if 'status' not in n:n['status']='open'
 counts={s:sum(n['status']==s for n in nodes) for s in ['split','certified','open']}
 # Exact tree integrity audit: reconstruct both child vertex tables, unique parent; no omitted child.
 seen={0}
 for n in nodes:
  if n['status']=='split':
   i,j,a,b=split(n['vertices']);assert [i,j]==n['edge']
   for child,vv in zip(n['children'],[a,b]):
    assert child not in seen;seen.add(child);assert nodes[child]['vertices']==vv
 assert seen==set(range(len(nodes)))
 # Leaf normalized8-volume is 2^-depth. Induction from midpoint determinant, not floating geometry.
 assert sum(F(1,2**n['depth']) for n in nodes if n['status']!='split')==1
 mass=sum(F(1,2**n['depth']) for n in nodes if n['status']=='certified')
 out={'status':'bounded pilot with unresolved leaves, NOT global','counts':counts,'certified_volume_fraction':str(mass),'fields':[{'name':ff['name'],'forces':[[str(x) for x in q] for q in ff['forces']]} for ff in fields],'nodes':[{**n,'vertices':[[str(x) for x in v] for v in n['vertices']]} for n in nodes]}
 (P/'simplex_tree_pilot.json').write_text(json.dumps(out,indent=2));print({'counts':counts,'certified_volume_fraction':str(mass),'maxdepth':max(n['depth'] for n in nodes)})
if __name__=='__main__':main()
