"""Bounded511 open cells with max64 adaptive stresses, C529 rational upper target. All exact DBM children persisted.
Each floating point oracle proposes scalar alpha only, exact rational Schur revalidated.
"""
from cosine_dbm_pilot import known_patch
from fractions import Fraction as F
TARGET=F(3799838531198387090485182,10**25) # C529 > exact R*, not equal
NUM_GATE=float(TARGET)+1e-9
from certify_cosine_polytope import *
from certify_energy_cell import schur
from cosine_cut_diagnostic import improve
import time,sys
sys.path.insert(0,str(P.parent/'r20-alternative'))
from fixed_oracle_v2 import propose_from_widths

def main():
 d=json.loads((P/'cosine_dbm_cuts.json').read_text());nodes=d['nodes'];fields=d['fields'];start=time.time()
 for n in nodes:n['db']=[[F(x) for x in row] for row in n['db']]
 queue=deque(n['id'] for n in nodes if n['status']=='open');proposals=[]
 for step in range(511):
  if not queue:break
  idx=queue.popleft();n=nodes[idx];pp=known_patch(n['db'])
  if pp:n.update({'status':'certified','patch':pp});continue
  _,r=improve(n['db'],fields,5);before=r['radius_lower_numeric']
  if before<=NUM_GATE and len(proposals)<64:
   y=np.maximum(0,np.array(r['y_numeric']));y/=sum(y)
   sol=propose_from_widths([float(lo(L))-float(lo(D))*t for t in y],maxiter=400)
   ff=schur([[F(float(x)) for x in q] for q in sol['p_51']],'dbm_local919'+str(idx));ff['weights']=[(i,j,str(w)) for i,j,w in ff['weights']];fields.append(ff)
   _,r=improve(n['db'],fields,5);proposals.append({'node':idx,'old_lower_numeric':before,'new_lower_numeric':r['radius_lower_numeric'],'point_oracle_numeric':sol['r'],'success':sol['success']})
  n['numeric_lower']=r['radius_lower_numeric']
  if r['radius_lower_numeric']>NUM_GATE:
   cc=certify(n['db'],r,fields,TARGET)
   if cc['certified_gt_target']:n.update({'status':'certified','certificate':cc});continue
  pair=r['branch_pair'];mid,a,b=branches(n['db'],pair);assert a is not None and b is not None
  n.update({'status':'split','pair':pair,'midpoint':str(mid),'children':[]})
  for db in [a,b]:
   ni=len(nodes);n['children'].append(ni);nodes.append({'id':ni,'db':db,'status':'open','depth':n['depth']+1});queue.append(ni)
 visited={0}
 for n in nodes:
  if n['status']!='split':continue
  mid,a,b=branches(n['db'],n['pair']);assert str(mid)==n['midpoint'] and len(n['children'])==2
  for ch,db in zip(n['children'],[a,b]):assert ch not in visited and nodes[ch]['db']==db;visited.add(ch)
 assert visited==set(range(len(nodes)))
 summary={'scope':'bounded adaptive DBM run; all open leaves retained; NOT global','counts':{s:sum(n['status']==s for n in nodes) for s in ['split','certified','open']},'seconds':time.time()-start,'new_proposals':len(proposals),'field_count':len(fields)}
 (P/'cosine_dbm_local919.json').write_text(json.dumps({'summary':summary,'proposals':proposals,'fields':fields,'nodes':[{**n,'db':[[str(x) for x in row] for row in n['db']]} for n in nodes]},indent=2));print(summary,flush=True)
if __name__=='__main__':main()
