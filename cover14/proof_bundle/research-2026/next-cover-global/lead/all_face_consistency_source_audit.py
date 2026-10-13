"""Bind streamed replay inputs to final producer objects and exact exclusion union."""
import json,hashlib
from fractions import Fraction as F
from pathlib import Path
P=Path(__file__).resolve().parent
load=lambda n:json.loads((P/n).read_text())
key=lambda x:(x['row']['family'],x['row']['index'])
full=load('all-face-consistency-catalogue.json')['runs'];stream=[json.loads(s)for s in (P/'all-face-consistency-catalogue.jsonl').read_text().splitlines()];fm={key(x):x for x in full};sm={key(x):x for x in stream};assert len(fm)==len(full)==436 and fm==sm
old={(x['family'],x['index'])for x in load('shared-radius-retained.json')['retained']};assert set(fm)==old
re=load('all-face-consistency-catalogue-fraction-replay.json');assert re['producer_count']==436
rr={(x['family'],x['index']):x for x in re['runs']};ss=[json.loads(s)for s in (P/'all-face-consistency-catalogue-fraction.jsonl').read_text().splitlines()];assert len(rr)==len(re['runs'])==80 and rr=={(x['family'],x['index']):x for x in ss};assert all(F(x['upper_exact'])<0 for x in rr.values());assert set(rr)=={key(x)for x in full if x['certificate']['status']=='excluded'}
small={(x['family'],x['index'])for x in load('all-face-consistency-fraction-replay.json')['runs']};assert len(small)==5 and small<=set(rr)
u=load('all-face-consistency-full-retained.json');assert {(x['family'],x['index'])for x in u['retained']}==old-set(rr);assert u['remaining_count']==356
names=['all-face-consistency-catalogue.json','all-face-consistency-catalogue.jsonl','all-face-consistency-catalogue-fraction-replay.json','all-face-consistency-catalogue-fraction.jsonl','all-face-consistency-full-retained.json','k10-catalogue-corrected.json','q11-pocket-catalogue.json','all_face_consistency_fraction_replay.py','shared_radius_corner_fraction_kernel.py']
out={'status':'source_and_union_exact_audit_passed','producer_count':436,'replayed_negative':80,'bounded_five_overlap':5,'remaining':356,'counts':u['counts'],'scope':'input binding and exact set bookkeeping; mathematical kernel validity inherited from C1246','sha256':{n:hashlib.sha256((P/n).read_bytes()).hexdigest()for n in names}};(P/'all-face-consistency-source-audit.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items()if k!='sha256'})
