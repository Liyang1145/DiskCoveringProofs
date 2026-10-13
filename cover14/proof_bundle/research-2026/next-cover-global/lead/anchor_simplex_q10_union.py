"""Hashbound 83wholeangularsimplex exclusions; no candidate/extraction relabeling."""
import json,hashlib,collections
from pathlib import Path
from fractions import Fraction as F
P=Path(__file__).resolve().parent
prev=json.loads((P/'face-support-exchange-retained.json').read_text());ret={(x['family'],x['index'])for x in prev['retained']};cs=P/'anchor-simplex-q10-certificates.json';cert=json.loads(cs.read_text());rep=json.loads((P/'anchor-simplex-q10-fraction-replay.json').read_text());assert rep['source_sha256']==hashlib.sha256(cs.read_bytes()).hexdigest();cr={(r['family'],r['index']):r for r in cert['runs']};excluded=[]
for row in rep['runs']:
 key=(row['family'],row['index']);assert key in ret and key in cr;assert row['excluded']and F(row['lower_radius_exact'])>F('.33173203427623414')and F(cr[key]['lower_radius_exact'])>F('.33173203427623414');ret.remove(key);excluded.append(key)
assert len(excluded)==83 and len(ret)==272
out={'status':'necessary_catalogue_after_global_angular_simplex_exclusions','previous_count':len(prev['retained']),'remaining_count':len(ret),'counts':dict(collections.Counter(f for f,i in ret)),'new_exclusions':[{'family':f,'index':i}for f,i in excluded],'source_sha256':{name:hashlib.sha256((P/name).read_bytes()).hexdigest()for name in ['face-support-exchange-retained.json','anchor-simplex-q10-certificates.json','anchor-simplex-q10-fraction-replay.json','k10-catalogue-corrected.json']},'retained':[{'family':f,'index':i}for f,i in sorted(ret)]};(P/'anchor-simplex-q10-retained.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items()if k not in ['new_exclusions','source_sha256','retained']})
