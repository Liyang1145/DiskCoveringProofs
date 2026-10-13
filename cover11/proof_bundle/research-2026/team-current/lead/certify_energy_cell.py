"""Exact rational Schur weights, interval energy game on node26 and two children.
No dependence on correctness of numeric stress proposals. Units V^2.
"""
from multifield_simplex_pilot import *
import sympy as sp

def schur(raw,name):
 vals=np.linalg.norm(np.array([[float(F(x)) for x in row] for row in raw]),axis=1)
 # Positive integers force connectivity of all free nodes; no numerical rank premise.
 ints=[max(1,round(float(x)*10**9)) for x in vals];S=sum(ints)
 alpha=[sp.Rational(x,S) for x in ints];assert sum(alpha)==1 and min(alpha)>0
 LL=sp.zeros(31)
 for (v,w),a in zip(edges,alpha):LL[v,v]+=a;LL[w,w]+=a;LL[v,w]-=a;LL[w,v]-=a
 ff=LL[9:,9:];fa=LL[9:,:9];sol=ff.inv()*fa;assert ff*sol==fa
 M=LL[:9,:9]-LL[:9,9:]*sol
 assert M==M.T and M*sp.ones(9,1)==sp.zeros(9,1)
 weights=[]
 for i in range(9):
  for j in range(i+1,9):
   w=F(-M[i,j]);assert w>=0;weights.append((i,j,w))
 print('exact Schur complete',name,flush=True)
 return {'name':name,'alpha':[str(x) for x in alpha],'weights':weights}

def row(verts,field):
 theta=[angles(v) for v in verts];vals=[iv.mpf(0) for _ in verts];pen=iv.mpf(0)
 for i,j,w in field['weights']:
  # Difference computed directly from affine y-prefixes to avoid independent-angle wrapping.
  zz=[(i-j)*L-D*I(sum(v[:i])-sum(v[:j])) for v in verts]
  a=min(lo(x) for x in zz);b=max(hi(x) for x in zz);arc=iv.mpf([a,b])
  c=hi(2*I(w)*iv.cos(arc));c=max(mp.mpf(0),c)
  pen+=iv.mpf(c)*(iv.mpf(b)-iv.mpf(a))**2/8
  for k,z in enumerate(zz):vals[k]+=2*I(w)*(1-iv.cos(z))
 return [v-pen for v in vals]

def main():
 d=json.loads((P/'adaptive_stellar_pilot.json').read_text());want=['corner4','adaptive1','adaptive21'];fields=[]
 for f in d['fields']:
  if f['name'] in want:fields.append(schur(f['forces'],f['name']))
 assert len(fields)==3
 node=d['nodes'][26];v=[[F(x) for x in r] for r in node['vertices']];i,j,a,b=split(v)
 rows=[]
 for label,vv in [('node26',v),('childA',a),('childB',b)]:
  A=[row(vv,f) for f in fields];lb,beta=game(A)
  rows.append({'cell':label,'vertices':[[str(x) for x in r] for r in vv],'energy_lower':str(lb),'radius_lower':str(lo(iv.sqrt(iv.mpf(lb)))) if lb>0 else None,'beta':[str(x) for x in beta],'status':'certified' if iv.mpf(lb)>I(F(19,50))**2 else 'open'})
 out={'scope':'three exact positive scalar stresses; node26 and one midpoint subdivision only; NOT global','rows':rows,'fields':[{**f,'weights':[(i,j,str(w)) for i,j,w in f['weights']]} for f in fields]}
 (P/'energy_cell_certificate.json').write_text(json.dumps(out,indent=2));print([(r['cell'],r['radius_lower'],r['status']) for r in rows])
if __name__=='__main__':main()
