"""Rational cumulative-sum cell representation, numerical LP proposals.
Cells are difference-bound matrices on t0=0,t9=1,tj−ti=sum y[i:j].
DBM closure is exact Fraction shortest path, no guessed polytope vertices.
"""
from cosine_envelope_lp_diagnostic import intercept,pairs
from simplex_tree_pilot import *
import numpy as np
from scipy.optimize import linprog

def rootdbm():
 # db[i][j] upper-bounds t_j-t_i. y>=0 implies t_i-t_j<=0 for i<j.
 db=[[F(0) if j<=i else F(1) for j in range(10)] for i in range(10)]
 db[9][0]=F(-1);return closure(db)

def closure(db):
 db=[r[:] for r in db]
 for k in range(10):
  for i in range(10):
   for j in range(10):
    db[i][j]=min(db[i][j],db[i][k]+db[k][j])
 if any(db[i][i]<0 for i in range(10)):return None
 return db

def branches(db,pair):
 i,j=pair;l,u=-db[j][i],db[i][j];assert l<u
 mid=(l+u)/2;left=[r[:] for r in db];right=[r[:] for r in db];left[i][j]=mid;right[j][i]=-mid
 return mid,closure(left),closure(right)

def domain_rows(db):
 A=[];b=[]
 for i in range(10):
  for j in range(i+1,10):
   row=[F(int(i<=k<j)) for k in range(9)];A.extend([row,[-x for x in row]]);b.extend([db[i][j],db[j][i]])
 return A,b

def solve(db,fields,cuts=None):
 m=len(pairs);nv=9+m+1;A=[];rhs=[];lines=[];Lnum=float(lo(L));Dnum=float(lo(D))
 for k,(i,j) in enumerate(pairs):
  l,u=-db[j][i],db[i][j];a=(i-j)*Lnum+Dnum*float(l);b=(i-j)*Lnum+Dnum*float(u)
  slopes=sorted(set([0.,-1.,1.]+[float(np.sin(z)) for z in np.linspace(a,b,9)]+([(np.cos(a)-np.cos(b))/(b-a)] if b>a else [])+(cuts[k] if cuts else [])))
  zrow=np.array([Dnum if i<=q<j else 0 for q in range(9)])
  for s in slopes:
   v=intercept(a,b,s);row=np.zeros(nv);row[:9]=s*zrow;row[9+k]=-1;A.append(row);rhs.append(-v-s*(i-j)*Lnum);lines.append({'pair':k,'slope':s})
 for f in fields:
  row=np.zeros(nv)
  for k,(i,j,w) in enumerate(f['weights']):row[9+k]=2*float(F(w))
  row[-1]=-1;A.append(row);rhs.append(0)
 da,bb=domain_rows(db)
 for ar,b in zip(da,bb):A.append(np.r_[np.array(ar,dtype=float),np.zeros(m+1)]);rhs.append(float(b))
 eq=np.zeros((1,nv));eq[0,:9]=1;c=np.zeros(nv);c[-1]=1
 res=linprog(c,A_ub=A,b_ub=rhs,A_eq=eq,b_eq=[1],bounds=[(0,None)]*9+[(None,None)]*(m+1),method='highs');assert res.success,res.message
 beta=-res.ineqlin.marginals[len(lines):len(lines)+len(fields)];W=np.array([sum(beta[f]*2*float(F(fields[f]['weights'][k][2])) for f in range(len(fields))) for k in range(m)])
 y=res.x[:9];loss=[]
 for k,(i,j) in enumerate(pairs):
  z=(i-j)*Lnum+Dnum*sum(y[i:j]);width=float(db[i][j]+db[j][i]);loss.append((W[k]*max(0,1-np.cos(z)-res.x[9+k]),width,k))
 # Prefer highest relaxation gap; tie deterministic. Never split a zero-width direction.
 _,_,k=max(x for x in loss if x[1]>0)
 return {'energy_lower_numeric':res.fun,'radius_lower_numeric':float(np.sqrt(max(0,res.fun))),'y_numeric':y.tolist(),'dual_ineq_numeric':res.ineqlin.marginals.tolist(),'lines':lines,'branch_pair':list(pairs[k]),'largest_pair_gap':loss[k][0]}
