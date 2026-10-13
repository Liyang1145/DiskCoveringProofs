"""Independent scalar-rational coverage and exactflowreplay for configured exteriorround."""
from q10_rational_polytope_audit import *
from q11_chord_flow_fraction_replay import replay
import sys
if __name__=='__main__':
 cfg=json.loads((P/sys.argv[1]).read_text());base=P/cfg['domain'];BV,bc=decode(json.loads(base.read_text())['polytope']);autos=json.loads((P/'q10-fan-transport.json').read_text())['runs'];results=[];cuts=set()
 for ix,case in enumerate(cfg['cases']):
  src=P/f"{cfg['stem']}-{ix}.json"
  if not src.exists():continue
  raw=src.read_bytes();a=json.loads(raw);assert a['source_sha256']==hashlib.sha256(base.read_bytes()).hexdigest()and a['case']==case;nodes=a['nodes'];pending=set(a['pending']);ids,t,sgn=case;normal=tuple(Q(sgn)*int(i in ids)for i in range(10));rhs=Q(sgn)*Q(t);V,_=clip(BV,bc,normal,rhs);cs=bc+[(normal,rhs)];todo=[(0,V,cs)];seen=set();leaves=[];openrows=[]
  while todo:
   j,V,cs=todo.pop();assert j not in seen;seen.add(j);n=nodes[j];assert n['id']==j
   if j in pending:assert 'status'not in n;openrows.append({'node':j,'vertices':len(V)});continue
   assert decode(n['polytope'])==(V,cs)
   if n['status']=='split':
    rep=n['split_report'];nn=tuple(map(Q,rep['normal']));rr=scalar(rep['rhs']);ge,le=clip(V,cs,nn,rr)
    for child,s,childV in zip(n['children'],[1,-1],[ge,le]):todo.append((child,childV,cs+[(tuple(s*x for x in nn),s*rr)]))
   else:
    assert n['status']=='leaf_bound_coverage_pending';c=n['certificate'];assert c['index']==879 and {tuple(scalar(t)for t in v)for v in c['polytope']['vertices']}==V;rr=replay(c);assert rr['excluded'];leaves.append({'node':j,'lower_exact':rr['lower_radius_exact']})
  assert seen==set(range(len(nodes)));results.append({'case':case,'source_sha256':hashlib.sha256(raw).hexdigest(),'nodes':len(nodes),'excluded_leaves':leaves,'open_cells':openrows})
  if not pending:
   for g in autos:
    dg={int(k):v for k,v in g['deficit_permutation'].items()};cuts.add((tuple(sorted(dg[i]for i in ids)),'greater'if sgn==-1 else'less',t))
  out={'status':'sourcebound_configured_exterior_audit','domain_sha256':hashlib.sha256(base.read_bytes()).hexdigest(),'results':results,'cuts':[{'indices':list(ids),'sense':s,'fraction_of_total':t}for ids,s,t in sorted(cuts)]};(P/f"{cfg['stem']}-audit.json").write_text(json.dumps(out,indent=2));print('METRICAUDIT',cfg['stem'],ix,len(nodes),len(leaves),len(openrows),flush=True)
