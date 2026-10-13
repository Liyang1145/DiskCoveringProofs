"""Atmost31 robust-flow simplexnodes perhardq10type, proposes completebinarypartitions."""
from anchor_robust_flow_probe import solve,P,json,np,math
from anchor_simplex_subdivision_probe import solve_node
import time,sys
L=2*math.asin(.33173203427623414);delta=10*L-2*math.pi
for idx in map(int,sys.argv[1:]or['848','878','879']):
 base=next(r for r in json.loads((P/'anchor-simplex-q10-catalogue-probe.json').read_text())['runs']if r['index']==idx);nodes=[{'id':0,'V':np.eye(10).tolist()}];pending=[0];processed=0
 saved=P/f'anchor-robust-subdivision-warm-{idx}.json'
 if saved.exists():
  prev=json.loads(saved.read_text());nodes=prev['nodes'];pending=prev['pending'];processed=prev['processed']
 stop=processed+127
 while pending and processed<stop:
  k=pending.pop();node=nodes[k];V=np.array(node['V']);local,_,_=solve_node(idx,base['faces'],V);local.update(index=idx,family='10/4');row=solve(local,10,'concave',V);node['flow_proposal']=row;processed+=1
  if row['robust_value']>.3318:node['status']='proposed_excluded'
  else:
   T=np.array([np.arange(10)*L-delta*np.r_[0,np.cumsum(v[:-1])]for v in V]);dist=((T[:,None,:]-T[None,:,:])**2).sum(axis=2);s,t=np.unravel_index(np.argmax(dist),dist.shape);mid=(V[s]+V[t])/2;V1=V.copy();V2=V.copy();V1[s]=mid;V2[t]=mid;children=[]
   for VV in [V1,V2]:
    j=len(nodes);nodes.append({'id':j,'V':VV.tolist()});children.append(j)
   node.update(status='split',split_edge=[int(s),int(t)],children=children);pending.extend(children)
  (P/f'anchor-robust-subdivision-warm-{idx}.json').write_text(json.dumps({'status':'numeric_robust_partition_proposals','family':'10/4','index':idx,'nodes':nodes,'pending':pending,'processed':processed},indent=2))
 print('DONE',idx,'nodes',processed,'pending',len(pending),flush=True)
