"""Numeric calibration and mechanism comparison ONLY. No certification."""
from simplex_tree_pilot import *
import numpy as np
from scipy.optimize import linprog

def stress(p):
 alpha=np.linalg.norm(np.array(p,dtype=float),axis=1);alpha/=alpha.sum()
 lap=np.zeros((31,31))
 for (v,w),a in zip(edges,alpha):lap[v,v]+=a;lap[w,w]+=a;lap[v,w]-=a;lap[w,v]-=a
 # alpha tiny/zero disconnected auxiliaries are isolated; use Moore-Penrose numerically for diagnostic only.
 LL=lap[:9,:9]-lap[:9,9:]@np.linalg.pinv(lap[9:,9:],rcond=1e-13)@lap[9:,:9]
 return [(i,j,max(0.,-LL[i,j])) for i in range(9) for j in range(i+1,9)],alpha

def evalrow(verts,st):
 theta=np.array([[float(lo(x)) for x in angles(v)] for v in verts]);vals=np.zeros(len(verts));pen=0.
 for i,j,w in st:
  z=theta[:,i]-theta[:,j];a,b=z.min(),z.max();cmax=max(np.cos(a),np.cos(b))
  if np.ceil(a/(2*np.pi))<=np.floor(b/(2*np.pi)):cmax=1.
  pen+=2*w*max(0,cmax)*(b-a)**2/8
  vals+=2*w*(1-np.cos(z))
 return vals-pen

def main():
 data=json.loads((P/'adaptive_stellar_pilot.json').read_text());fields=[]
 for f in data['fields']:
  st,alpha=stress([[float(F(x)) for x in row] for row in f['forces']]);fields.append((f['name'],st))
 base=json.loads((P.parent/'r20-alternative/fixed_oracle_force_proposal.json').read_text())['points']
 calibrations=[]
 for s in base:
  st,aa=stress(s['force_vectors_51']);th=np.r_[0,np.cumsum(s['widths'])[:-1]]
  E=sum(2*w*(1-np.cos(th[i]-th[j])) for i,j,w in st)
  calibrations.append({'name':s['name'],'energy':E,'r2':s['r']**2,'gap':E-s['r']**2})
 out=[]
 for n in data['nodes'][:31]:
  verts=[[F(x) for x in row] for row in n['vertices']]
  arr=np.array([evalrow(verts,st) for name,st in fields]);m=len(arr)
  rr=linprog(np.r_[np.zeros(m),-1],A_ub=np.c_[-arr.T,np.ones(9)],b_ub=np.zeros(9),A_eq=[np.r_[np.ones(m),0]],b_eq=[1],bounds=[(0,None)]*m+[(None,None)],method='highs')
  assert rr.success
  bound=-rr.fun;out.append({'node':n['id'],'energy_game':bound,'sqrt_nonnegative':np.sqrt(max(0,bound)),'old_force_radius':float(n['lower']),'weights':[(fields[k][0],float(x)) for k,x in enumerate(rr.x[:m]) if x>1e-9]})
 summary={'label':'NUMERIC ONLY; clipped roundoff, pinv, LP not certificates','calibrations':calibrations,'rows':out,'best_sqrt':max(x['sqrt_nonnegative'] for x in out),'threshold2':.38**2}
 (P/'energy_cell_diagnostic.json').write_text(json.dumps(summary,indent=2));print('calibration',calibrations);print('best',summary['best_sqrt']);print('root',out[0]);print('wins',sum(x['sqrt_nonnegative']>x['old_force_radius'] for x in out),'of',len(out))
if __name__=='__main__':main()
