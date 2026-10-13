"""Bounded12graphs probe:newcertifiedinnernormline, geometryclassification analyticdraft."""
import json
from itertools import combinations
import area_capped_chord_probe as C
from innernorm_line_certificate import A,k
from area_safe_certificate import P,Q
C.A=A;C.k=k;C.T=(C.Lb-A)/k
D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());saved=[json.loads(x)for x in(P/'area-capped-chord-catalogue.jsonl').read_text().splitlines()];out=[]
for fam in ['10/4','11/3']:
 rr=sorted([x for x in saved if x['family']==fam and x['status']=='inconclusive'],key=lambda x:x['upper_display'])[:6]
 for row in rr:
  q=int(fam.split('/')[0]);idx=row['index'];faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});rec=C.solve_cert(14,q,edges,list(map(Q,row['rational_angles'])));rec.update(family=fam,index=idx);out.append(rec);print(fam,idx,rec['status'],rec.get('upper_display'),flush=True)
(P/'innernorm-envelope-probe.json').write_text(json.dumps({'status':'exact_interval_bounds_conditional_geometry_interface','A':str(A),'k':str(k),'Lbar':str(C.Lb),'runs':out},indent=2))
