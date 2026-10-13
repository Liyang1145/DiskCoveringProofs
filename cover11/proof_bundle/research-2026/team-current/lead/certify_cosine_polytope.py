"""Interval affine minorant + exact rational inequality dual with simplex residual.
For Ay<=b,lambda>=0 and y simplex: f0+c.y>=f0-lambda.b+min_i(c+A.T lambda)_i.
No numerical feasibility claim is promoted. Each residual explicitly retained.
"""
from cosine_polytope import *
from certify_cosine_envelope_cell import normalize,intercept as cert_intercept

def certify(db,row,fields,target=F(19,50)):
 lines=row['lines'];dual=row['dual_ineq_numeric'];beta=normalize([-x for x in dual[len(lines):len(lines)+len(fields)]])
 W=[sum(beta[f]*2*F(fields[f]['weights'][k][2]) for f in range(len(fields))) for k in range(36)]
 assert sum(beta)==1 and min(beta)>=0 and min(W)>=0
 c=[iv.mpf(0) for _ in range(9)];f0=iv.mpf(0);records=[]
 for k,(i,j) in enumerate(pairs):
  inds=[t for t,line in enumerate(lines) if line['pair']==k];gamma=normalize([-dual[t] for t in inds]);assert sum(gamma)==1 and min(gamma)>=0
  aa=(i-j)*L+D*I(-db[j][i]);bb=(i-j)*L+D*I(db[i][j]);a,b=lo(aa),hi(bb);subset=[]
  for t,g in zip(inds,gamma):
   if not g:continue
   s=F(float(lines[t]['slope']));v=cert_intercept(a,b,s);weight=W[k]*g
   f0+=I(weight)*(I(s)*(i-j)*L+iv.mpf(v))
   for q in range(i,j):c[q]+=I(weight*s)*D
   subset.append({'slope':str(s),'gamma':str(g),'intercept_lower':str(v)})
  records.append({'pair':[i,j],'weight':str(W[k]),'arc':[str(a),str(b)],'lines':subset})
 A,b=domain_rows(db);lam=[F(max(0,round(-x*10**12)),10**12) for x in dual[len(lines)+len(fields):]]
 assert len(lam)==len(A) and min(lam)>=0
 residual=[c[k]+I(sum(lam[j]*A[j][k] for j in range(len(A)))) for k in range(9)]
 lb=lo(f0-I(sum(x*y for x,y in zip(lam,b))))+min(lo(x) for x in residual)
 # Re-evaluate outward sum, never use rounded mp addition as a bearing lower endpoint.
 lb=lo((f0-I(sum(x*y for x,y in zip(lam,b))))+iv.mpf(min(lo(x) for x in residual)))
 return {'energy_lower':str(lb),'certified_gt_19_50':bool(iv.mpf(lb)>I(F(19,50))**2),'target':str(target),'certified_gt_target':bool(iv.mpf(lb)>I(target)**2),'beta':[str(x) for x in beta],'lambda':[str(x) for x in lam],'minorants':records,'residual_min_lower':str(min(lo(x) for x in residual))}
