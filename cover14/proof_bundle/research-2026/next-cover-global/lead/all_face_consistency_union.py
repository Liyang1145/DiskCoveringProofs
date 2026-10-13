"""Run only after full Fraction replay finishes; union independently replayed exclusions."""
import json,collections,hashlib
from pathlib import Path
P=Path(__file__).resolve().parent
old=json.loads((P/'shared-radius-retained.json').read_text())['retained'];ret={(x['family'],x['index'])for x in old};ex=set();sources=[]
full=json.loads((P/'all-face-consistency-catalogue.json').read_text())['runs'];expected={(x['row']['family'],x['row']['index'])for x in full if x['certificate']['status']=='excluded'}
for name in ['all-face-consistency-catalogue-fraction-replay.json','all-face-consistency-fraction-replay.json']:
 data=json.loads((P/name).read_text())['runs'];ss={(x['family'],x['index'])for x in data};assert len(ss)==len(data);assert ss<=ret
 if name.startswith('all-face-consistency-catalogue-'):assert ss==expected
 ex|=ss;sources.append({'file':name,'count':len(ss),'sha256':hashlib.sha256((P/name).read_bytes()).hexdigest()})
remaining=ret-ex;counts=dict(collections.Counter(f for f,i in remaining));out={'status':'necessary_systems_after_independent_fraction_replays','previous_count':len(ret),'excluded_union':len(ex),'remaining_count':len(remaining),'counts':counts,'sources':sources,'excluded':[{'family':f,'index':i}for f,i in sorted(ex)],'retained':[{'family':f,'index':i}for f,i in sorted(remaining)]};(P/'all-face-consistency-full-retained.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items()if k not in['excluded','retained']})
