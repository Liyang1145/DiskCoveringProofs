"""Three bounded jointCartesian+orderedanchor localcontrols; NOTglobalbounds."""
from fixed_anchor_convex_probe import *
import sys

def run(row):
 q=len(row['anchors']);D=np.array(row['incidence_matrix']);nf=len(row['faces']);nv=D.shape[1];m=len(D);X=np.array(row['centers']+row['witnesses']);t0=np.unwrap(np.arctan2(np.array(row['anchors'])[:,1],np.array(row['anchors'])[:,0]));assert abs(t0[0])<1e-10;A=np.c_[np.cos(t0),np.sin(t0)];offset=np.zeros((m,2));offset[3*nf:]=-np.repeat(A,2,axis=0);rr=np.linalg.norm(D@X+offset,axis=1).max();x0=np.r_[X.ravel(),rr,t0[1:]];N=2*nv+1+q-1;L=2*math.asin(.33173203427623414)
 def con(x,jac=False):
  X=x[:2*nv].reshape(nv,2);r=x[2*nv];t=np.r_[0,x[2*nv+1:]];A=np.c_[np.cos(t),np.sin(t)];Tan=np.c_[-np.sin(t),np.cos(t)];offset=np.zeros((m,2));offset[3*nf:]=-np.repeat(A,2,axis=0);p=D@X+offset;l=np.linalg.norm(p,axis=1);gap=np.diff(np.r_[t,2*math.pi]);v=np.r_[r-l,gap,L-gap]
  if not jac:return v
  u=p/np.maximum(l[:,None],1e-30);J=np.zeros((m+2*q,N))
  for k in range(2):J[:m,k:2*nv:2]=-u[:,k,None]*D
  J[:m,2*nv]=1
  for j in range(1,q):J[3*nf+2*j:3*nf+2*j+2,2*nv+j]=u[3*nf+2*j:3*nf+2*j+2]@Tan[j]
  for j in range(q):
   if j>0:J[m+j,2*nv+j]-=1
   if j+1<q:J[m+j,2*nv+j+1]+=1
  J[m+q:]=-J[m:m+q];return J
 grad=np.zeros(N);grad[2*nv]=1;opt=minimize(lambda x:x[2*nv],x0,jac=lambda x:grad,method='SLSQP',constraints=[{'type':'ineq','fun':con,'jac':lambda x:con(x,True)}],options={'maxiter':300,'ftol':2e-13});t=np.r_[0,opt.x[2*nv+1:]];out={'case':row['case'],'status':'numeric_only_outer_local','radius':float(opt.x[2*nv]),'initial_radius':float(rr),'success':bool(opt.success),'iterations':int(opt.nit),'min_constraint':float(min(con(opt.x))),'angles':t.tolist(),'centers':opt.x[:28].reshape(14,2).tolist(),'witnesses':opt.x[28:2*nv].reshape(nf,2).tolist(),'faces':row['faces'],'owners':row['owners']};print({k:v for k,v in out.items()if k not in ['centers','witnesses','faces','owners','angles']},flush=True);return out
if __name__=='__main__':
 data=json.loads((P/'anchor-simplex-q10-catalogue-probe.json').read_text())['runs'];out=[]
 for idx in map(int,sys.argv[1:]or['848','878','879']):out.append(run(next(r for r in data if r['index']==idx)));(P/'anchor-outer-local-probe.json').write_text(json.dumps({'status':'numeric_only_three_jointlocaltests','runs':out},indent=2))
