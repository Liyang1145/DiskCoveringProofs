"""75 near cells, bounded cutting-plane diagnostic; optional exact certificates.
Slopes at LP adversaries, intercept always whole interval. Numeric gate never proof.
"""
from certify_cosine_polytope import *
import time
TARGET=F(3799838531198387090485182,10**25)
def improve(db,fields,rounds=8):
 cuts=[[] for _ in pairs];r=solve(db,fields);before=r['radius_lower_numeric']
 for _ in range(rounds):
  y=r['y_numeric']
  for k,(i,j) in enumerate(pairs):cuts[k].append(float(np.sin((i-j)*float(lo(L))+float(lo(D))*sum(y[i:j]))))
  rr=solve(db,fields,cuts);gain=rr['energy_lower_numeric']-r['energy_lower_numeric'];r=rr
  if gain<1e-11:break
 return before,r

def main():
 d=json.loads((P/'cosine_dbm_near.json').read_text());rows=[];start=time.time()
 for n in d['nodes']:
  if n['status']!='open':continue
  db=[[F(x) for x in z] for z in n['db']];before,r=improve(db,d['fields']);cc=certify(db,r,d['fields'],TARGET) if r['radius_lower_numeric']>float(TARGET)+1e-10 else None
  rows.append({'node':n['id'],'before_numeric':before,'after_numeric':r['radius_lower_numeric'],'certificate':cc,'y_numeric':r['y_numeric']})
 out={'scope':'cutting-plane diagnostic, original75open retained in source','seconds':time.time()-start,'certified':sum(bool(x['certificate'] and x['certificate']['certified_gt_target']) for x in rows),'rows':rows}
 (P/'cosine_cut_diagnostic.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items() if k!='rows'})
if __name__=='__main__':main()
