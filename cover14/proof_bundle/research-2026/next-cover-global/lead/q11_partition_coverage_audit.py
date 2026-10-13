"""Sourcebinding and exactclosed-halfspace partitioncoverage + independentleafbounds."""
from q11_chord_polytope import P,json,Q,chord_middles,enumerate_vertices
from q11_chord_flow_fraction_replay import replay
import hashlib,sys
for idx in map(int,sys.argv[1:]or['510','75']):
 src=P/f'q11-polytope-partition-{idx}.json';a=json.loads(src.read_text());audit=P/f'q11-split-inductive-audit-{idx}.json';b=json.loads(audit.read_text());assert not a['pending'];assert b['source_sha256']==hashlib.sha256(src.read_bytes()).hexdigest();nodes=a['nodes'];assert all(r['exact_vertexsets_equal']for r in b['runs']);assert {r['node']for r in b['runs']}==set(range(len(nodes)));row=nodes[0]['flow_proposal'];root=enumerate_vertices(chord_middles(row['faces']));canon=lambda vv:{tuple(tuple(map(Q,t))for t in v)for v in vv};assert canon(root['vertices'])==canon(nodes[0]['polytope']['vertex_set']);rc=nodes[0]['polytope']['inequalities'][22:];assert len(rc)==len(root['middles_owner'])
 for (nn,rr,lab),i in zip(rc,root['middles_owner']):assert list(map(Q,nn))==[Q(j in {(i-2)%11,(i-1)%11,i})for j in range(11)]and list(map(Q,rr))==[Q(3),Q(-1),Q(0)]
 source=json.loads((P/'q11-pocket-catalogue.json').read_text())['entries'][idx]['faces'];assert row['faces']==source and row['index']==idx and a['index']==idx
 rp=nodes[0]['polytope'];assert rp['equality']==[['1']*11,['11','0','-1']]
 for j in range(11):
  nn,rr,_=rp['inequalities'][2*j];assert list(map(Q,nn))==[Q(i==j)for i in range(11)]and list(map(Q,rr))==[Q(0)]*3
  nn,rr,_=rp['inequalities'][2*j+1];assert list(map(Q,nn))==[-Q(i==j)for i in range(11)]and list(map(Q,rr))==[Q(-1),Q(0),Q(0)]
 seen=set();todo=[0];leaves=[]
 while todo:
  j=todo.pop();assert j not in seen;seen.add(j);n=nodes[j];assert n['id']==j
  if n['status']=='split':
   children=n['children'];assert len(children)==2 and children[0]!=children[1];p=n['polytope'];rep=n['split_report'];normal=list(map(Q,rep['normal']));rhs=list(map(Q,rep['rhs']));assert len(normal)==11 and len(rhs)==3
   for child,sgn in zip(children,[1,-1]):
    c=nodes[child]['polytope'];assert c['equality']==p['equality'];assert c['inequalities'][:-1]==p['inequalities'];nn,rr,lab=c['inequalities'][-1];assert list(map(Q,nn))==[sgn*x for x in normal]and list(map(Q,rr))==[sgn*x for x in rhs]
   todo.extend(children)
  else:
   assert n['status']=='leaf_bound_certified_coverage_pending';assert n['certificate']['index']==idx and n['certificate']['flow']['faces']==source;assert canon(n['certificate']['polytope']['vertices'])==canon(n['polytope']['vertex_set']);r=replay(n['certificate']);assert r['excluded']and Q(r['lower_radius_exact'])>Q('.33173203427623414');leaves.append({'node':j,'lower_radius_exact':r['lower_radius_exact']})
 assert seen==set(range(len(nodes)));lo=min(Q(r['lower_radius_exact'])for r in leaves);out={'status':'complete_sourcebound_polytope_partition_exclusion','index':idx,'nodes':len(nodes),'leaves':len(leaves),'minimum_lower_exact':str(lo),'minimum_lower_display':float(lo),'sources':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in [src,audit]},'leafbounds':leaves};(P/f'q11-partition-coverage-audit-{idx}.json').write_text(json.dumps(out,indent=2));print('CERTIFIED',idx,len(nodes),len(leaves),float(lo))
