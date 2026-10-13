"""131 open leaves, existing three exact Schur stresses only, cosine envelope LP.
Interval certify every numerical positive; retain all noncertified leaves.
"""
from cosine_envelope_lp_diagnostic import solve
from certify_cosine_envelope_cell import certify
from simplex_tree_pilot import *
import time

def main():
 import sys
 full='--full' in sys.argv
 d=json.loads((P/('energy_library.json' if full else 'energy_cell_certificate.json')).read_text());fields=d['fields'];tree=json.loads((P/'adaptive_stellar_pilot.json').read_text());out=[];started=time.time()
 for node in tree['nodes']:
  if node['status']!='open':continue
  v=[[F(x) for x in r] for r in node['vertices']];r=solve(v,fields);r.update({'cell':str(node['id']),'vertices':node['vertices']});record={'node':node['id'],'mass':node['mass'],'radius_lower_numeric':r['radius_lower_numeric'],'status':'open'}
  if r['radius_lower_numeric']>.380001:
   cert=certify(r,fields)
   if cert['certified_gt_19_50']:record.update({'status':'certified','certificate':cert})
  out.append(record)
 counts={s:sum(r['status']==s for r in out) for s in ['certified','open']};mass=sum(F(r['mass']) for r in out if r['status']=='certified')
 assert sum(F(r['mass']) for r in out)==1
 summary={'counts':counts,'certified_mass':str(mass),'seconds':time.time()-started,'field_count':len(fields),'scope':'131 open leaves from saved exact stellar tree; fixed scalar stress library; all remaining leaves retained; NOT global'}
 (P/('cosine_leaf_full_pilot.json' if full else 'cosine_leaf_pilot.json')).write_text(json.dumps({'summary':summary,'fields':fields,'leaves':out},indent=2));print(summary)
if __name__=='__main__':main()
