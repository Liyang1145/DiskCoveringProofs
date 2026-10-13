"""Configurable bounded exterior-stripping experiment. Exactaudits separate.
CLI config.json. Each case [indices, rational threshold inD, side(+1 >=,-1<=)].
Writes one resumable tree per case; no completeness claim until scalar audit.
"""
from q10_reduced_metric_domain import *
from q10_polytope_partition_probe import Polytope,default_decider,midrange_split
import sys,hashlib
from q10_mean_gauge_bound import mean_bound

def load(p):return Polytope(10,[tuple(tuple(map(Q,t))for t in v)for v in p['vertex_set']],[(list(map(Q,n)),tuple(map(Q,r)),lab)for n,r,lab in p['inequalities']],(list(map(Q,p['equality'][0])),tuple(map(Q,p['equality'][1]))),default_decider(),'879')
if __name__=='__main__':
 cfgpath=P/sys.argv[1];cfg=json.loads(cfgpath.read_text());base=P/cfg['domain'];raw=base.read_bytes();root=load(json.loads(raw)['polytope']);sourcehash=hashlib.sha256(raw).hexdigest();row=next(r for r in json.loads((P/'anchor-simplex-q10-catalogue-probe.json').read_text())['runs']if r['index']==879)
 for ix,(ids,t,sgn)in enumerate(cfg['cases']):
  saved=P/f"{cfg['stem']}-{ix}.json";rhs=tuple(sgn*Q(t)*x for x in tri(10,0,-1));cp,_,rootrep=root.split([sgn*int(i in ids)for i in range(10)],rhs,f"{cfg['stem']}_{ix}");nodes=[{'id':0}];pending=[0];polys=[cp]
  if saved.exists():
   a=json.loads(saved.read_text());assert a['source_sha256']==sourcehash and a['case']==[ids,t,sgn];nodes=a['nodes'];pending=a['pending'];polys=[load(n['polytope'])if 'polytope'in n else None for n in nodes]
   for n in nodes:
    if n.get('status')=='split'and any(polys[j]is None for j in n['children']):
     rep=n['split_report'];ch=polys[n['id']].split(list(map(Q,rep['normal'])),tuple(map(Q,rep['rhs'])),rep['label'])[:2]
     for j,p in zip(n['children'],ch):
      if polys[j]is None:polys[j]=p
  for step in range(cfg['budget_per_case']):
   if not pending:break
   j=pending.pop();poly=polys[j];TT=angles(poly);AA=np.c_[np.cos(TT.mean(axis=0)),np.sin(TT.mean(axis=0))];nf=len(row['faces']);D=np.array(row['incidence_matrix']);rhs=np.vstack([np.zeros((3*nf,2)),np.repeat(AA,2,axis=0)]);X=np.linalg.lstsq(D,rhs,rcond=None)[0];r=solve_case(row['case'],X[:14],AA,row['faces'],row['owners'],X[14:]);r.update(index=879,family='10/4');r=smooth(r,TT);c=bound(r,{'vertices':poly.to_dict()['vertex_set']});n=nodes[j];n.update(polytope=poly.to_dict(),flow_proposal=r)
   if c['status']!='excluded_pending_fraction_replay':
    r,c,rr=mean_bound(row,poly);n.update(flow_proposal=r)
   else:rr=replay(c)
   if rr['excluded']:
    n.update(status='leaf_bound_coverage_pending',certificate=c,replay=rr)
   else:
    centered=TT-TT.mean(axis=1)[:,None];k=int(np.argmax(np.ptp(centered,axis=0)));normal=[9-i-10*int(i<k)for i in range(10)];ge,le,rep,_=midrange_split(poly,normal,f"{cfg['stem']}_{ix}_{j}_meanangle{k}");ch=[]
    for p in [ge,le]:ch.append(len(nodes));nodes.append({'id':len(nodes)});polys.append(p)
    n.update(status='split',split_report=rep,children=ch);pending.extend(ch)
   saved.write_text(json.dumps({'status':'exterior_coverage_pending','source_sha256':sourcehash,'domain':cfg['domain'],'case':[ids,t,sgn],'root_split':rootrep,'nodes':nodes,'pending':pending},indent=2));print('METRICROUND',cfg['stem'],ix,j,len(poly.vertices),c['lower_radius_display'],len(pending),flush=True)
