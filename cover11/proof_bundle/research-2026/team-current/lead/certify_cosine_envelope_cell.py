"""Exact rational dual mixture of whole-interval cosine affine minorants.
LP proposes weights only. No LP optimality/feasibility premise in certificate.
"""
from simplex_tree_pilot import *
import math
pairs=[(i,j) for i in range(9) for j in range(i+1,9)]

def normalize(values):
 qq=[F(max(0,round(float(x)*10**12)),10**12) for x in values]
 if sum(qq)==0:qq=[F(1,len(qq))]*len(qq)
 return [q/sum(qq) for q in qq]

def intercept(a,b,s):
 # All critical points of g(z)-s z satisfy sin z=s; endpoints also considered.
 assert -1<=s<=1
 roots=[];u=iv.atan2(I(s),iv.sqrt(1-I(s)**2))
 candidates=[iv.mpf(a),iv.mpf(b)]
 for base in [u,iv.pi-u]:
  for k in range(-3,4):
   zz=base+2*k*iv.pi
   if hi(zz)<a or lo(zz)>b:continue
   candidates.append(zz)
 # Coverage guard: [a,b] within[-2pi,2pi], branches k=-3..3 certainly exhaustive.
 assert a>lo(-2*iv.pi) and b<hi(2*iv.pi)
 vals=[1-iv.cos(z)-I(s)*z for z in candidates]
 return min(lo(v) for v in vals)

def certify(row,fields):
 v=[[F(x) for x in r] for r in row['vertices']];lines=row['lines'];dual=row['dual_ineq_numeric'];beta=normalize([-x for x in dual[len(lines):]])
 assert len(beta)==len(fields) and sum(beta)==1 and min(beta)>=0
 W=[sum(beta[f]*F(fields[f]['weights'][k][2])*2 for f in range(len(fields))) for k in range(36)]
 assert min(W)>=0
 vals=[iv.mpf(0) for _ in range(9)];records=[]
 for k,(i,j) in enumerate(pairs):
  inds=[t for t,line in enumerate(lines) if line['pair']==k]
  gamma=normalize([-dual[t] for t in inds]);assert sum(gamma)==1 and min(gamma)>=0
  zz=[(i-j)*L-D*I(sum(y[:i])-sum(y[:j])) for y in v];a=min(lo(z) for z in zz);b=max(hi(z) for z in zz)
  subset=[]
  for t,g in zip(inds,gamma):
   if g==0:continue
   s=F(float(lines[t]['slope']));bb=intercept(a,b,s)
   for vv,z in enumerate(zz):vals[vv]+=I(W[k]*g)*(I(s)*z+iv.mpf(bb))
   subset.append({'slope':str(s),'gamma':str(g),'intercept_lower':str(bb)})
  records.append({'pair':[i,j],'weight':str(W[k]),'arc':[str(a),str(b)],'lines':subset})
 lb=min(lo(x) for x in vals)
 return {'cell':row['cell'],'energy_lower':str(lb),'radius_lower':str(lo(iv.sqrt(iv.mpf(lb)))),'certified_gt_19_50':bool(iv.mpf(lb)>I(F(19,50))**2),'beta':[str(x) for x in beta],'vertices':row['vertices'],'minorants':records}

def main():
 d=json.loads((P/'cosine_envelope_lp_diagnostic.json').read_text());fields=d['fields']
 # Schur weights came from exact rational algebra in certify_energy_cell.py; no floating Schur premiss.
 for f in fields:assert [(i,j) for i,j,w in f['weights']]==pairs
 results=[certify(row,fields) for row in d['rows'] if row['cell']=='node26']
 assert all(r['certified_gt_19_50'] for r in results)
 out={'status':'proved-interval on node26 only; NOT global','proof':'Each cosine has certified global affine minorants on full cell difference interval; convex gamma gives minorant; beta energy mix gives V² lower; resulting affine function minimized at simplex vertices. LP numbers propose rational beta/gamma only.','rows':results,'fields':fields}
 (P/'cosine_envelope_cell_certificate.json').write_text(json.dumps(out,indent=2));print([(r['cell'],r['radius_lower']) for r in results])
if __name__=='__main__':main()
