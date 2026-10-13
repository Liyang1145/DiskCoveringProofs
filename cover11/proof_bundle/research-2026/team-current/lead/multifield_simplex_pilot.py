"""Bounded127-node exact y-tree with mixed support LP proposals.
LP solves only for rational combination proposals. Interval validation bears lowerbound.
"""
from simplex_tree_pilot import *
import numpy as np
from scipy.optimize import linprog

def table(vertices,fields):
 th=[angles(v) for v in vertices]
 cs=[[(iv.cos(t),iv.sin(t)) for t in ts] for ts in th]
 arcs=[]
 for i in range(9):
  a=min(lo(ts[i]) for ts in th);b=max(hi(ts[i]) for ts in th);arc=iv.mpf([a,b])
  arcs.append((iv.cos(arc),iv.sin(arc),(iv.mpf(b)-iv.mpf(a))**2/8))
 A=[]
 for ff in fields:
  loads=ff['loads'];pen=iv.mpf(0)
  for i,(c,s,factor) in enumerate(arcs):
   val=I(loads[i][0])*c+I(loads[i][1])*s
   pen+=iv.mpf(max(mp.mpf(0),-lo(val)))*factor
  A.append([sum(I(loads[i][0])*cv[i][0]+I(loads[i][1])*cv[i][1] for i in range(9))-pen for cv in cs])
 return A

def game(A):
 f=len(A);arr=np.array([[float(lo(v)) for v in row] for row in A])
 obj=np.r_[np.zeros(f),-1.0]
 res=linprog(obj,A_ub=np.c_[-arr.T,np.ones(9)],b_ub=np.zeros(9),A_eq=np.array([np.r_[np.ones(f),0.0]]),b_eq=[1.0],bounds=[(0,None)]*f+[(None,None)],method='highs')
 # The maximizer is not needed. Any nonnegative rational normalized weights yield a rigorous bound.
 if res.success:weights=[F(max(0,round(v*10**10)),10**10) for v in res.x[:f]]
 else:
  j=max(range(f),key=lambda k:min(lo(v) for v in A[k]));weights=[F(i==j) for i in range(f)]
 S=sum(weights);assert S>0;weights=[w/S for w in weights];assert sum(weights)==1 and min(weights)>=0
 works=[sum(I(weights[k])*A[k][j] for k in range(f)) for j in range(9)]
 return min(lo(w) for w in works),weights

def main():
 cert=json.loads((P/'uniform_sector_certificate.json').read_text());assert [tuple(e) for e in cert['edges']]==edges
 fields=[field([[F(x) for x in q] for q in cert['forces_rational']],'C911')]
 for s in json.loads((P/'corner_simplex_certificates.json').read_text())['rows']:
  assert s['status']=='proved-interval';fields.append(field([[F(x) for x in q] for q in s['forces']],'corner'+str(s['corner'])))
 base=json.loads((P.parent/'r20-alternative/fixed_oracle_force_proposal.json').read_text())['points']
 for s in base:fields.append(field(repair(s['force_vectors_51']),s['name']))
 # Known patch calibration against single-field result.
 t=F(19,50);patch=[[F(1-t,9)+(t if i==j else 0) for i in range(9)] for j in range(9)]
 assert game(table(patch,fields))[0]>mp.mpf(19)/50
 root=[[F(i==j) for i in range(9)] for j in range(9)]
 nodes=[{'id':0,'vertices':root,'depth':0}];queue=deque([0]);processed=0
 while queue and processed<127:
  idx=queue.popleft();n=nodes[idx];A=table(n['vertices'],fields);lb,beta=game(A);single=max(min(lo(v) for v in row) for row in A)
  n.update({'lower':str(lb),'single_field_lower':str(single),'beta':[str(w) for w in beta]});processed+=1
  if lb>mp.mpf(19)/50:n['status']='certified';continue
  i,j,a,b=split(n['vertices']);n.update({'status':'split','edge':[i,j],'children':[len(nodes),len(nodes)+1]})
  for vv in [a,b]:
   nxt=len(nodes);nodes.append({'id':nxt,'vertices':vv,'depth':n['depth']+1});queue.append(nxt)
 for n in nodes:
  if 'status' not in n:n['status']='open'
 seen={0}
 for n in nodes:
  if n['status']=='split':
   i,j,a,b=split(n['vertices']);assert [i,j]==n['edge']
   for ch,vv in zip(n['children'],[a,b]):assert ch not in seen;seen.add(ch);assert nodes[ch]['vertices']==vv
 assert seen==set(range(len(nodes)))
 assert sum(F(1,2**n['depth']) for n in nodes if n['status']!='split')==1
 counts={s:sum(n['status']==s for n in nodes) for s in ['split','certified','open']}
 mass=sum(F(1,2**n['depth']) for n in nodes if n['status']=='certified')
 summary={'counts':counts,'certified_volume_fraction':str(mass),'max_gain':str(max(mp.mpf(n['lower'])-mp.mpf(n['single_field_lower']) for n in nodes if 'lower'in n))}
 out={'status':'boundedpilot_NOT_GLOBAL','summary':summary,'fields':[{'name':f['name'],'forces':[[str(x) for x in q] for q in f['forces']]} for f in fields],'nodes':[{**n,'vertices':[[str(x) for x in v] for v in n['vertices']]} for n in nodes]}
 (P/'multifield_simplex_pilot.json').write_text(json.dumps(out,indent=2));print(summary)
if __name__=='__main__':main()
