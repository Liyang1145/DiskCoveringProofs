"""Independent scalar rational coverage of named exterior partition; no global promotion."""
from q10_rational_polytope_audit import *
from q11_chord_flow_fraction_replay import replay
import sys
if __name__=='__main__':
 ix=int(sys.argv[1]);stem=f'q10-exterior-partition-{ix}';src=P/(stem+'.json');raw=src.read_bytes();a=json.loads(raw);nodes=a['nodes'];pending=set(a['pending']);V,cs=decode(nodes[0]['polytope']);control=P/'q10-c1337-slab-controls.json';assert a['source_sha256']==hashlib.sha256(control.read_bytes()).hexdigest();row=json.loads(control.read_text())['runs'][ix];assert decode(row['polytope'])==(V,cs);base=json.loads((P/'q10-c1337-domain.json').read_text());BV,bc=decode(base['polytope']);assert cs[:-1]==bc;n,r=cs[-1];assert n==tuple(Q(row['side'])*int(i in row['indices'])for i in range(10)) and r==Q(row['side'])*Q(row['threshold_total_fraction']);EV,_=clip(BV,bc,n,r);assert V==EV;faces=json.loads((P/'k10-catalogue-corrected.json').read_text())['10/4'][879]['faces'];todo=[(0,V,cs)];seen=set();leaves=[];openrows=[]
 while todo:
  j,V,cs=todo.pop();assert j not in seen;seen.add(j);n=nodes[j];assert n['id']==j
  if j in pending:assert 'status'not in n;openrows.append({'node':j,'vertices':len(V)});continue
  VV,cc=decode(n['polytope']);assert VV==V and cc==cs
  if n['status']=='split':
   rep=n['split_report'];normal=tuple(map(Q,rep['normal']));rhs=scalar(rep['rhs']);ge,le=clip(V,cs,normal,rhs)
   for child,s,childV in zip(n['children'],[1,-1],[ge,le]):todo.append((child,childV,cs+[(tuple(s*x for x in normal),s*rhs)]))
  else:
   assert n['status']=='leaf_bound_coverage_pending';c=n['certificate'];assert c['index']==879 and c['flow']['faces']==faces and {tuple(scalar(t)for t in v)for v in c['polytope']['vertices']}==V;rr=replay(c);assert rr['excluded'];leaves.append({'node':j,'lower_exact':rr['lower_radius_exact']})
  print('EXTERIORTREE',ix,j,len(V),flush=True)
 assert seen==set(range(len(nodes)));out={'status':'independent_partial_exterior_coverage'if pending else'complete_exterior_exclusion','source_sha256':hashlib.sha256(raw).hexdigest(),'domain_sha256':hashlib.sha256((P/'q10-c1337-domain.json').read_bytes()).hexdigest(),'indices':row['indices'],'side':row['side'],'threshold':row['threshold_total_fraction'],'nodes':len(nodes),'excluded_leaves':leaves,'open_cells':openrows};(P/(stem+'-audit.json')).write_text(json.dumps(out,indent=2));print('EXTERIORDONE',ix,len(nodes),len(leaves),len(openrows),flush=True)
