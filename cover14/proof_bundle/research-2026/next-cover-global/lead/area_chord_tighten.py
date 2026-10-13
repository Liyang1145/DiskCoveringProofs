"""Named obligation: eliminate the sole remainingq10/m3 graph via tighteranalytic chord envelope."""
import json
from itertools import combinations
import area_chord_probe as K
from area_safe_certificate import I,Q,S,U,asin,trig,P
A=Q('0.333272257');k=Q('0.123099267');a0=Q('2.420575')
sn,cs=trig(I(a0)/2);z=I(U)*sn;f=2*I(asin(Q(z.lo,S)).lo,asin(Q(z.hi,S)).hi,True);fp=I(U)*cs/(1-z*z).sqrt();b=f-I(a0)*fp
margins=[I(A)-2*asin(U/2),I(k)-fp,I(A)-b]
assert all(x.lo>0 for x in margins)
K.A=A;K.k=k
D=json.loads((P/'k10-catalogue-corrected.json').read_text());faces=D['10/3'][62]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)})
row=next(json.loads(x)for x in(P/'area-chord-catalogue.jsonl').read_text().splitlines()if json.loads(x)['family']=='10/3' and json.loads(x)['index']==62)
rec=K.solve_cert(13,10,edges,list(map(Q,row['rational_angles'])));rec.update(family='10/3',index=62)
(P/'area-chord-tighten.json').write_text(json.dumps({'status':'exact_interval','scope':'sole remainingq10/m3 graphindex62','A':str(A),'k':str(k),'a0':str(a0),'envelope_margins':[x.dec()for x in margins],'runs':[rec]},indent=2));print(rec['status'],rec.get('upper_display'))
