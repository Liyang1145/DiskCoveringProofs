"""Union only independently replayed certificates with C1229 retainedset."""
import json,collections,hashlib
from pathlib import Path
P=Path(__file__).resolve().parent
old=json.loads((P/'pack-reopt-retained.json').read_text())['retained'];ret={(x['family'],x['index'])for x in old};ex=set();sources=[]
for name in ['shared-radius-catalogue-fraction-replay.json','shared-radius-corner-fraction-replay.json']:
 data=json.loads((P/name).read_text())['runs'];ss={(x['family'],x['index'])for x in data};assert len(ss)==len(data);assert ss<=ret;ex|=ss;sources.append({'file':name,'count':len(ss),'sha256':hashlib.sha256((P/name).read_bytes()).hexdigest()})
remaining=ret-ex;counts=dict(collections.Counter(f for f,i in remaining));out={'status':'necessary_systems_after_independent_fraction_replays','previous_count':len(ret),'excluded_union':len(ex),'remaining_count':len(remaining),'counts':counts,'sources':sources,'excluded':[{'family':f,'index':i}for f,i in sorted(ex)],'retained':[{'family':f,'index':i}for f,i in sorted(remaining)]};(P/'shared-radius-retained.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items()if k not in['excluded','retained']})
