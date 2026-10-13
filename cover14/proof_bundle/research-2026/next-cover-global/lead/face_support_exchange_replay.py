"""Independent rational replay of one adaptive-proposal certificate."""
from all_face_consistency_fraction_replay import *
import hashlib
start=time.time();name='face-support-exchange-certificate.json';src=json.loads((P/name).read_text());row=src['row'];cert=src['certificate'];assert row['family']=='10/4'and row['index']==547 and cert['status']=='excluded';faces=json.loads((P/'k10-catalogue-corrected.json').read_text())['10/4'][547]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});b=verify_all(10,edges,faces,row,cert);assert b[1]<0
out={'status':'independent_fraction_replay','family':'10/4','index':547,'upper_exact':str(b[1]),'upper_display':float(b[1]),'source_sha256':hashlib.sha256((P/name).read_bytes()).hexdigest(),'seconds':time.time()-start};(P/'face-support-exchange-replay.json').write_text(json.dumps(out,indent=2));print(out,flush=True)
