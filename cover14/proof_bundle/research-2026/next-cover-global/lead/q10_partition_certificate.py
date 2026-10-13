"""Exactdyadicbinarypartitioncoverage+directedandFractionboundsoneveryterminalsimplex."""
from q11_chord_flow_certificate import bound,P,json,Q
from q11_chord_flow_fraction_replay import replay
import sys,hashlib
for idx in map(int,sys.argv[1:]or['878']):
 src=P/f'anchor-robust-subdivision-warm-{idx}.json';data=json.loads(src.read_text());nodes=data['nodes'];seen=set();cert=[];rep=[]
 def parse(V):return [tuple(Q(x)for x in v)for v in V]
 def visit(k,expected):
  assert k not in seen;seen.add(k);node=nodes[k];V=parse(node['V']);assert V==expected and all(sum(v)==1 and min(v)>=0 for v in V)
  if node['status']=='split':
   s,t=node['split_edge'];assert 0<=s<10 and 0<=t<10 and s!=t;mid=tuple((x+y)/2 for x,y in zip(V[s],V[t]));V1=V.copy();V2=V.copy();V1[s]=mid;V2[t]=mid;a,b=node['children'];visit(a,V1);visit(b,V2)
  else:
   assert node['status']=='proposed_excluded';poly={'vertices':[[[str(10*x),'0',str(-x)]for x in v]for v in V],'vertex_count':10,'domain':'dyadicq10simplexnode','id':k};c=bound(node['flow_proposal'],poly);assert c['status']=='excluded_pending_fraction_replay',(idx,k,c['lower_radius_display']);r=replay(c);assert r['excluded'];cert.append(c);rep.append(r);print('EXACT',idx,k,r['lower_radius_display'],flush=True)
 root=[tuple(Q(int(i==j))for j in range(10))for i in range(10)];assert not data['pending'];visit(0,root);assert len(seen)==len(nodes);out={'status':'complete_simplex_partition_exclusion','family':'10/4','index':idx,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'nodes':len(seen),'leaves':len(cert),'minimum_lower_display':min(r['lower_radius_display']for r in rep),'certificates':cert,'fraction_replays':rep};(P/f'q10-partition-{idx}-certificate.json').write_text(json.dumps(out,indent=2));print('DONE',idx,out['nodes'],out['leaves'],out['minimum_lower_display'],flush=True)
