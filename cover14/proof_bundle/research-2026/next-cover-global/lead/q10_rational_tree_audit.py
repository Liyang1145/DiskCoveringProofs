"""Scalar rational independenttreecoverage andleafreplay; partialtrees explicitlyremainpartial."""
from q10_rational_polytope_audit import *
from q11_chord_flow_fraction_replay import replay
import sys
if __name__=='__main__':
 stem=sys.argv[1]if len(sys.argv)>1 else'q10-reduced-partition';src=P/(stem+'.json');raw=src.read_bytes();a=json.loads(raw);nodes=a['nodes'];pending=set(a['pending']);V,cs=decode(nodes[0]['polytope']);base=json.loads((P/'q10-reduced-metric-domain.json').read_text())['polytope'];VV,cc=decode(base);assert V==VV and cs==cc;da=json.loads((P/'q10-reduced-domain-audit.json').read_text());assert da['source_sha256']==hashlib.sha256((P/'q10-reduced-metric-domain.json').read_bytes()).hexdigest();assert V=={tuple(map(Q,v))for v in da['normalized_vertices']};faces=json.loads((P/'k10-catalogue-corrected.json').read_text())['10/4'][879]['faces'];todo=[(0,V,cs)];seen=set();leaves=[];openrows=[]
 while todo:
  j,V,cs=todo.pop();assert j not in seen;seen.add(j);n=nodes[j];assert n['id']==j
  if j in pending:assert 'status'not in n;openrows.append({'node':j,'vertices':len(V)});continue
  VV,cc=decode(n['polytope']);assert VV==V and cc==cs
  if n['status']=='split':
   rep=n['split_report'];normal=tuple(map(Q,rep['normal']));rhs=scalar(rep['rhs']);ge,le=clip(V,cs,normal,rhs)
   for child,s,childV in zip(n['children'],[1,-1],[ge,le]):todo.append((child,childV,cs+[(tuple(s*x for x in normal),s*rhs)]))
  else:
   assert n['status']=='leaf_bound_coverage_pending';c=n['certificate'];assert c['index']==879 and c['flow']['faces']==faces and {tuple(scalar(t)for t in v)for v in c['polytope']['vertices']}==V;rr=replay(c);assert rr['excluded'];leaves.append({'node':j,'lower_exact':rr['lower_radius_exact']})
  print('RATIONALTREE',j,len(V),flush=True)
 assert seen==set(range(len(nodes)));out={'status':'independent_partial_rational_tree_coverage'if pending else'complete_rational_tree_exclusion','source_sha256':hashlib.sha256(raw).hexdigest(),'nodes':len(nodes),'excluded_leaves':leaves,'open_cells':openrows};(P/(stem+'-rational-audit.json')).write_text(json.dumps(out,indent=2));print('RATIONALTREEDONE',len(nodes),len(leaves),len(openrows),flush=True)
