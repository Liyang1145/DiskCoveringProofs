"""Numeric only convex piecewise-affine scalar energy relaxation.
All line intercepts minimize g(z)-s*z over full cell interval, not local tangents.
"""
from simplex_tree_pilot import *
import numpy as np
from scipy.optimize import linprog
import math
pairs=[(i,j) for i in range(9) for j in range(i+1,9)]

def intercept(a,b,s):
 pts=[a,b]
 if abs(s)<=1:
  u=math.asin(s)
  for root in [u,math.pi-u]:
   for k in range(-3,4):
    z=root+2*math.pi*k
    if a<=z<=b:pts.append(z)
 return min(1-math.cos(z)-s*z for z in pts)

def solve(verts,fields):
 th=np.array([[float(lo(x)) for x in angles(v)] for v in verts]);zv=np.array([th[:,i]-th[:,j] for i,j in pairs]);m=len(pairs);nv=9+m+1
 A=[];rhs=[];lines=[]
 for k,(i,j) in enumerate(pairs):
  a,b=zv[k].min(),zv[k].max()
  slopes=sorted(set([0.,-1.,1.]+[float(math.sin(z)) for z in np.linspace(a,b,9)]+[(math.cos(a)-math.cos(b))/(b-a)] if b>a else [math.sin(a)]))
  for s in slopes:
   v=intercept(a,b,s);row=np.zeros(nv);row[:9]=s*zv[k];row[9+k]=-1
   A.append(row);rhs.append(-v);lines.append({'pair':k,'slope':s,'intercept':v,'zlo':a,'zhi':b})
 for f in fields:
  row=np.zeros(nv)
  for i,j,w in f['weights']:row[9+pairs.index((i,j))]=2*float(F(w))
  row[-1]=-1;A.append(row);rhs.append(0)
 eq=np.zeros((1,nv));eq[0,:9]=1;c=np.zeros(nv);c[-1]=1
 res=linprog(c,A_ub=np.array(A),b_ub=rhs,A_eq=eq,b_eq=[1],bounds=[(0,None)]*9+[(None,None)]*(m+1),method='highs')
 assert res.success
 return {'energy_lower_numeric':res.fun,'radius_lower_numeric':math.sqrt(max(0,res.fun)),'lambda_numeric':res.x[:9].tolist(),'dual_ineq_numeric':res.ineqlin.marginals.tolist(),'dual_eq_numeric':res.eqlin.marginals.tolist(),'lines':lines}

def main():
 data=json.loads((P/'energy_cell_certificate.json').read_text());fields=data['fields'];tree=json.loads((P/'adaptive_stellar_pilot.json').read_text());rows=[]
 cells=[('root',[[F(i==j) for i in range(9)] for j in range(9)])]+[(r['cell'],[[F(x) for x in v] for v in r['vertices']]) for r in data['rows']]
 for name,v in cells:
  row=solve(v,fields);row['cell']=name;row['vertices']=[[str(x) for x in r] for r in v];rows.append(row);print(name,row['radius_lower_numeric'],flush=True)
 out={'scope':'NUMERIC ONLY, exact weights but ordinary float intercept/LP','fields':fields,'rows':rows}
 (P/'cosine_envelope_lp_diagnostic.json').write_text(json.dumps(out,indent=2))
if __name__=='__main__':main()
