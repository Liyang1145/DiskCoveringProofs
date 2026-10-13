"""Three fixedanchor convex controls; global-simplex flow tests numeric only."""
from fixed_anchor_convex_probe import *
from itertools import combinations

def case(name,q,faces,owners):
 n=14;nf=len(faces);nv=n+nf;A=np.array([[math.cos(2*math.pi*j/q),math.sin(2*math.pi*j/q)]for j in range(q)]);rows=[];rhs=[]
 for j,f in enumerate(faces):
  for v in f:
   d=np.zeros(nv);d[v]=1;d[n+j]=-1;rows.append(d);rhs.append([0,0])
 for j,vs in enumerate(owners):
  for v in vs:
   d=np.zeros(nv);d[v]=1;rows.append(d);rhs.append(A[j])
 X=np.linalg.lstsq(np.array(rows),np.array(rhs),rcond=None)[0];row=solve_case(name,X[:n],A,faces,owners,X[n:]);z=np.array(row['flow_vectors']);b=z[3*nf:].reshape(q,2,2).sum(axis=1);g=-b;den=np.linalg.norm(z,axis=1).sum();L=2*math.asin(.33173203427623414);delta=q*L-2*math.pi;verts=[]
 if q==10:
  for i in range(q):d=np.zeros(q);d[i]=delta;verts.append(d)
 else:
  for i in range(q):
   for j in range(q):
    if i==j:continue
    d=np.zeros(q);d[i]=L;d[j]=delta-L;verts.append(d)
 T=np.array([np.arange(q)*L-np.r_[0,np.cumsum(d[:-1])]for d in verts]);t0=2*math.pi*np.arange(q)/q;A0=np.column_stack([np.cos(t0),np.sin(t0)]);B0=np.column_stack([-np.sin(t0),np.cos(t0)]);F0=(g*A0).sum();grad=(g*B0).sum(axis=1);bounds=F0+(T-t0)@grad-.5*((T-t0)**2)@np.linalg.norm(g,axis=1);termmin=[]
 for j in range(q):
  lo=min(T[:,j]);hi=max(T[:,j]);phi=math.atan2(g[j,1],g[j,0]);vals=[g[j]@np.array([math.cos(t),math.sin(t)])for t in [lo,hi]]
  for k in range(-2,3):
   t=phi+math.pi+2*k*math.pi
   if lo<=t<=hi:vals.append(-np.linalg.norm(g[j]))
  termmin.append(min(vals))
 direct=np.array([(g*np.column_stack([np.cos(t),np.sin(t)])).sum()for t in T]);row.update(q=q,global_taylor_vertex_lower_proposal=float(min(bounds)/den),all_terms_nonnegative_numeric=bool(min(termmin)>=-1e-12),minimum_term=float(min(termmin)),concave_vertex_lower_proposal=float(min(direct)/den),vertex_count=len(verts));print({k:row[k]for k in ['case','radius','global_taylor_vertex_lower_proposal','all_terms_nonnegative_numeric','minimum_term','concave_vertex_lower_proposal']},flush=True);return row
if __name__=='__main__':
 G=json.loads((P/'stress-barycentric-result.json').read_text());cases=[('candidate',10,[f['ids']for f in G['faces']]+[[4,6,12],[5,7,13]],[a['owners']for a in G['anchors']])];D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());cases += [('q10-391',10,D10['10/4'][391]['faces'],[[i,(i+1)%10]for i in range(10)]),('q11-58',11,D11['entries'][58]['faces'],[[i,(i+1)%11]for i in range(11)])];out=[]
 for name,q,faces,owners in cases:
  out.append(case(name,q,faces,owners));(P/'anchor-simplex-probe.json').write_text(json.dumps({'status':'numeric_flow_global_domain_proposals','runs':out},indent=2))
