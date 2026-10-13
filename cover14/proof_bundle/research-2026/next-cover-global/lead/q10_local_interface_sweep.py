"""Sourcebound localcell membership diagnostic of all currentopen cells; not exclusion."""
from q10_polytope_partition_probe import *
import importlib.util,hashlib
M=P.parent/'members'/'dirichlet-cut-audit-cc2'/'q10_local_cell_interface.py';spec=importlib.util.spec_from_file_location('local_member',M);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
if __name__=='__main__':
 src=P/'q10-polytope-partition-879.json';raw=src.read_bytes();a=json.loads(raw);pending=set(a['pending']);A,_=m.literal_geometry();maps=m.graph_maps();sigma=m.anchor_correspondence(maps[0]['phi'],m.literal_owners());psi,_=m.cumulative_literal_arcs(A,sigma);cyc=m.certify_literal_cycle(A);assert cyc['cycle_valid'];out=[]
 for n in a['nodes']:
  if n.get('status')!='split'or not any(i in pending for i in n['children']):continue
  p=n['polytope'];poly=Polytope(10,[tuple(tuple(map(Q,t))for t in v)for v in p['vertex_set']],[(list(map(Q,nn)),tuple(map(Q,rr)),lab)for nn,rr,lab in p['inequalities']],(list(map(Q,p['equality'][0])),tuple(map(Q,p['equality'][1]))),default_decider(),'879');rep=n['split_report'];children=poly.split(list(map(Q,rep['normal'])),tuple(map(Q,rep['rhs'])),rep['label'])[:2]
  for j,cp in zip(n['children'],children):
   if j not in pending:continue
   # Affine anchorangle extrema are obtained over completevertices. Reduce huge denominator
   # series intervals outward once to 40decimalrational endpoints, preserving enclosure.
   def rnd(t):return (Q(m._rat_str(t[0],40,-1)),Q(m._rat_str(t[1],40,1)))
   LI=rnd(m.L_IV);PI=rnd(m.TWO_PI);ps=[rnd(t)for t in psi];worst=Q(0);ranges=[]
   for k in range(10):
    vv=[]
    for v in cp.vertices:
     t=[Q(k),Q(0),Q(0)]
     for i in range(k):t=[x-y for x,y in zip(t,v[i])]
     assert t[1]==0;vv.append(m.iadd(m.imul(m.iv(t[0]),LI),m.imul(m.iv(t[2]),PI)))
    angle=(min(t[0]for t in vv),max(t[1]for t in vv));d=m.isub(angle,ps[k]);worst=max(worst,abs(d[0]),abs(d[1]));ranges.append([m._rat_str(x,30,s)for x,s in zip(d,[-1,1])])
   ok=worst<=m.EPS;out.append({'node':j,'vertices':len(cp.vertices),'pass':ok,'worst_upper_exact':m._rat_str(worst,30,1),'angle_difference_ranges':ranges});print('LOCALCELL',j,len(cp.vertices),ok,float(worst),flush=True)
 assert {r['node']for r in out}==pending;report={'status':'sourcebound_open_cell_membership_diagnostic','source_sha256':hashlib.sha256(raw).hexdigest(),'interface_sha256':hashlib.sha256(M.read_bytes()).hexdigest(),'runs':out,'scope':'false means notcertified inside sufficientcell, NOTinfeasible and NOTdisjointfromcell'};(P/'q10-local-interface-sweep.json').write_text(json.dumps(report,indent=2))
