"""Exact linear-algebra checks and cyclic-polygon calibration; no cover/continuum claim."""
import sympy as s,numpy as np,json
from pathlib import Path
P=Path(__file__).resolve().parent
out=[]
for q in [10,11]:
 M=s.zeros(q)
 for i in range(q):M[i,i]=1;M[i,(i-1)%q]=1
 rank=M.rank()
 if q%2:
  A=s.Matrix(q,q,lambda i,j:(-1)**((i-j)%q));assert M*A==2*s.eye(q)
 else:
  null=s.Matrix([(-1)**i for i in range(q)]);assert M*null==s.zeros(q,1);assert (null.T*M)==s.zeros(1,q)
 theta=np.array([1+0.13*np.cos(2*np.pi*i/q)for i in range(q)]);theta*=2*np.pi/theta.sum()
 phi=np.r_[0,np.cumsum(theta)[:-1]];v=np.column_stack([np.cos(phi),np.sin(phi)]);edges=np.roll(v,-1,axis=0)-v;length=np.linalg.norm(edges,axis=1);d=edges/length[:,None];tau=(theta+np.roll(theta,1))/2
 if q%2:err=float(max(abs(np.array(A,dtype=float)@tau-theta)))
 else:err=float(abs(np.dot(np.array([(-1)**i for i in range(q)]),tau)))
 # Deliberately perturb two missing edge lengths, observe exact linear vector identity numerically.
 j,k=0,q//3;mat=np.column_stack([d[j],d[k]]);det=float(np.linalg.det(mat));assert abs(det)>.1
 residual=edges.sum(axis=0);rest=sum((length[i]*d[i]for i in range(q)if i not in[j,k]),np.zeros(2));missing=np.linalg.solve(mat,-rest)
 out.append({'q':q,'exact_adjacent_sum_rank':rank,'turn_inverse_residual':err,'closed_edge_sum_residual':float(max(abs(residual))),'omitted_length_reconstruction_error':float(max(abs(missing-length[[j,k]]))),'nonparallel_determinant':det})
(P/'boundary-turn-elimination-control.json').write_text(json.dumps({'status':'exact_linear_algebra_and_numeric_polygon_controls','runs':out},indent=2));print(out)
