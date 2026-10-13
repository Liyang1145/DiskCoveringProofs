"""Bounded q10 simplex longest-edge bisection. Numeric only; saved dyadic partition and flows."""
from fixed_anchor_convex_probe import *
from fractions import Fraction as F
import contextlib,io,time,sys
U=.33173203427623414;L=2*math.asin(U);delta=10*L-2*math.pi

def solve_node(idx,faces,V):
 q=10;nf=len(faces);nv=14+nf;T=np.arange(q)*L-delta*np.c_[np.zeros(q),np.cumsum(V[:,:-1],axis=1)];t0=T.mean(axis=0);A=np.c_[np.cos(t0),np.sin(t0)];rows=[];rhs=[];owners=[[i,(i+1)%q]for i in range(q)]
 for j,f in enumerate(faces):
  for v in f:
   d=np.zeros(nv);d[v]=1;d[14+j]=-1;rows.append(d);rhs.append([0,0])
 for j,vs in enumerate(owners):
  for v in vs:
   d=np.zeros(nv);d[v]=1;rows.append(d);rhs.append(A[j])
 X=np.linalg.lstsq(np.array(rows),np.array(rhs),rcond=None)[0]
 with contextlib.redirect_stdout(io.StringIO()):row=solve_case('q10-'+str(idx),X[:14],A,faces,owners,X[14:])
 z=np.array(row['flow_vectors']);g=-z[3*nf:].reshape(q,2,2).sum(axis=1);den=np.linalg.norm(z,axis=1).sum();F0=(g*A).sum();grad=(g*np.c_[-np.sin(t0),np.cos(t0)]).sum(axis=1);bound=min(F0+(T-t0)@grad-.5*(T-t0)**2@np.linalg.norm(g,axis=1))/den
 return row,float(bound),T

def run(idx,budget=127):
 faces=json.loads((P/'k10-catalogue-corrected.json').read_text())['10/4'][idx]['faces'];nodes=[{'id':0,'V':np.eye(10).tolist()}];pending=[0];processed=0
 while pending and processed<budget:
  n=pending.pop();node=nodes[n];V=np.array(node['V']);row,b,T=solve_node(idx,faces,V);node.update(flow_proposal=row,lower_proposal=b);processed+=1
  if b>U+1e-7:node['status']='proposed_excluded'
  else:
   distances=((T[:,None,:]-T[None,:,:])**2).sum(axis=2);s,t=np.unravel_index(np.argmax(distances),distances.shape);mid=(V[s]+V[t])/2;V1=V.copy();V2=V.copy();V1[s]=mid;V2[t]=mid;children=[]
   for VV in [V1,V2]:
    j=len(nodes);nodes.append({'id':j,'V':VV.tolist()});children.append(j)
   node.update(status='split',split_edge=[int(s),int(t)],children=children);pending.extend(children)
  if processed%10==0:print(idx,'processed',processed,'pending',len(pending),'minradius',min(x['flow_proposal']['radius']for x in nodes if 'flow_proposal'in x),flush=True)
  (P/f'anchor-simplex-subdivision-{idx}.json').write_text(json.dumps({'status':'numeric_partition_proposals_only','family':'10/4','index':idx,'budget':budget,'processed':processed,'pending':pending,'nodes':nodes},indent=2))
 print('DONE',idx,processed,'pending',len(pending),'leaves',sum(x.get('status')=='proposed_excluded'for x in nodes),flush=True)
if __name__=='__main__':
 for idx in map(int,sys.argv[1:] or ['541','878']):run(idx)
