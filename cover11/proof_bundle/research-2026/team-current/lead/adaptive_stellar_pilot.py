"""31 examined cells, at most31 adaptive SOC proposals. Exact stellar tree.
Purpose: decide whether game-directed split+field corrects static-field blindspot.
Not a complete proof: every open leaf is persisted; no numerical solver result bears a claim.
"""
from multifield_simplex_pilot import *
import sys,time
sys.path.insert(0,str(P.parent/'r20-alternative'))
from fixed_oracle_v2 import propose_from_widths

def adversary(A):
 arr=np.array([[float(lo(x)) for x in row] for row in A]);m=len(A)
 res=linprog(np.r_[np.zeros(9),1.0],A_ub=np.c_[arr,-np.ones(m)],b_ub=np.zeros(m),A_eq=[np.r_[np.ones(9),0]],b_eq=[1],bounds=[(0,None)]*9+[(None,None)],method='highs')
 if not res.success:return [F(1,9)]*9
 lam=[F(max(0,round(x*10**8)),10**8) for x in res.x[:9]];s=sum(lam);assert s>0
 return [x/s for x in lam]

def main():
 d0=json.loads((P/'multifield_simplex_pilot.json').read_text())
 fields=[field([[F(x) for x in q] for q in f['forces']],f['name']) for f in d0['fields']]
 trial=json.loads((P/'adversarial_force_trial.json').read_text());fields.append(field([[F(x) for x in q] for q in trial['forces']],'adversarial0'))
 root=[[F(i==j) for i in range(9)] for j in range(9)]
 nodes=[{'id':0,'vertices':root,'depth':0,'mass':F(1),'status':'open'}];queue=deque([0]);proposals=[];started=time.time()
 # breadth-first preserves all open children and prevents hiding hard branches
 for step in range(31):
  if not queue:break
  idx=queue.popleft();n=nodes[idx];verts=n['vertices'];A=table(verts,fields);lb,beta=game(A);lam=adversary(A)
  if lb<=mp.mpf(19)/50:
   y=[sum(lam[j]*verts[j][i] for j in range(9)) for i in range(9)]
   widths=[float(lo(L-D*I(q))) for q in y]
   try:
    sol=propose_from_widths(widths,maxiter=400);ff=field(repair(sol['p_51']),'adaptive'+str(idx));fields.append(ff)
    point=lower([y]*9,ff)
    proposals.append({'node':idx,'success':sol['success'],'r':sol['r'],'point_support_lower':str(lo(point))})
    A=table(verts,fields);lb,beta=game(A);lam=adversary(A)
   except Exception as e:proposals.append({'node':idx,'error':str(e)})
  n.update({'lower':str(lb),'beta':[str(x) for x in beta],'fields_used':len(fields)})
  if lb>mp.mpf(19)/50:n['status']='certified';continue
  n['status']='split';children=[]
  if max(lam)>=F(98,100):
   i,j,a,b=split(verts);n.update({'kind':'midpoint','edge':[i,j]});parts=[(F(1,2),a),(F(1,2),b)]
  else:
   point=[sum(lam[j]*verts[j][i] for j in range(9)) for i in range(9)]
   n.update({'kind':'stellar','lambda':[str(x) for x in lam]});parts=[]
   for j,l in enumerate(lam):
    if l==0:continue
    vv=[r[:] for r in verts];vv[j]=point;parts.append((l,vv))
  for ratio,vv in parts:
   ni=len(nodes);children.append(ni);nodes.append({'id':ni,'vertices':vv,'depth':n['depth']+1,'mass':n['mass']*ratio,'status':'open'});queue.append(ni)
  n['children']=children
  print('step',step,'node',idx,'lb',float(lb),'fields',len(fields),'children',len(parts),flush=True)
 # Independent arithmetic replay of exact parent-child incidence and leafmass. Geometric coverage is ratio-minimum lemma.
 seen={0}
 for n in nodes:
  if n['status']!='split':continue
  if n['kind']=='midpoint':
   i,j,a,b=split(n['vertices']);assert n['edge']==[i,j];parts=[(F(1,2),a),(F(1,2),b)]
  else:
   lam=[F(x) for x in n['lambda']];assert sum(lam)==1 and min(lam)>=0
   point=[sum(lam[j]*n['vertices'][j][i] for j in range(9)) for i in range(9)];parts=[]
   for j,l in enumerate(lam):
    if l==0:continue
    vv=[r[:] for r in n['vertices']];vv[j]=point;parts.append((l,vv))
  assert len(parts)==len(n['children'])
  for ch,(ratio,vv) in zip(n['children'],parts):
   assert ch not in seen;seen.add(ch);assert nodes[ch]['vertices']==vv and nodes[ch]['mass']==n['mass']*ratio
 assert seen==set(range(len(nodes)))
 assert sum(n['mass'] for n in nodes if n['status']!='split')==1
 counts={s:sum(n['status']==s for n in nodes) for s in ['split','certified','open']};mass=sum(n['mass'] for n in nodes if n['status']=='certified')
 summary={'counts':counts,'certified_mass':str(mass),'seconds':time.time()-started,'field_count':len(fields)}
 out={'scope':'bounded adaptive pilot; open leaves persist; NOT global','summary':summary,'proposals':proposals,'fields':[{'name':f['name'],'forces':[[str(x) for x in q] for q in f['forces']]} for f in fields],'nodes':[{**n,'mass':str(n['mass']),'vertices':[[str(x) for x in v] for v in n['vertices']]} for n in nodes]}
 (P/'adaptive_stellar_pilot.json').write_text(json.dumps(out,indent=2));print(summary)
if __name__=='__main__':main()
