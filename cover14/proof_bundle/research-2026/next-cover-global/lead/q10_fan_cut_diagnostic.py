"""Exact range diagnostic of new structuralcuts on pending cells, no mutation."""
from q10_polytope_partition_probe import *
if __name__=='__main__':
 a=json.loads((P/'q10-polytope-partition-879.json').read_text());nodes=a['nodes'];pending=set(a['pending']);out=[]
 for node in nodes:
  if node.get('status')!='split'or not any(j in pending for j in node['children']):continue
  p=node['polytope'];poly=Polytope(10,[tuple(tuple(map(Q,t))for t in v)for v in p['vertex_set']],[(list(map(Q,n)),tuple(map(Q,r)),lab)for n,r,lab in p['inequalities']],(list(map(Q,p['equality'][0])),tuple(map(Q,p['equality'][1]))),default_decider(),'879');rep=node['split_report'];children=poly.split(list(map(Q,rep['normal'])),tuple(map(Q,rep['rhs'])),rep['label'])[:2]
  for j,cp in zip(node['children'],children):
   if j not in pending:continue
   ranges=[]
   for ids in [[8,9,0,1],[3,4,5,6]]:
    vals=[iv(tuple(sum(v[i][h]for i in ids)for h in range(3)))for v in cp.vertices];ranges.append([min(v.lo/S for v in vals),max(v.hi/S for v in vals)])
   out.append({'node':j,'vertices':len(cp.vertices),'ranges':ranges})
 (P/'q10-fan-cut-diagnostic.json').write_text(json.dumps({'status':'range_diagnostic_only','runs':out},indent=2));print(out)
