"""Extract all 29 physical support certificates without changing their values."""
from pathlib import Path
import hashlib,json,sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'vendor'))
import ijson

SOURCE=HERE/'native-recovered/n26-root25-current346-refit2-origin-append-composition-v1.json'
SHA='c1675552b56d762de0bca83ca3adbb28e06c71e95c94b387d7f216eee41187c9'
digest=hashlib.sha256()
with SOURCE.open('rb') as stream:
    for chunk in iter(lambda:stream.read(1024*1024),b''):digest.update(chunk)
if digest.hexdigest()!=SHA:raise ValueError('Wrong original support source')
dest=HERE/'supports';dest.mkdir(exist_ok=True)
rows=[]
with SOURCE.open('rb') as stream:
    for i,support in enumerate(ijson.items(stream,'full134rod_supports.item')):
        payload=(json.dumps(support,indent=2)+'\n').encode()
        name='support-'+str(i).zfill(2)+'.json'
        (dest/name).write_bytes(payload)
        kernel=support['kernel_certificate']
        if len(kernel['weight_numerators'])!=134 or len(kernel['inverse_numerators'])!=60:
            raise ValueError('Unexpected physical support dimensions')
        rows.append({'index':i,'file':name,'sha256':hashlib.sha256(payload).hexdigest(),
            'weight_scale':kernel['weight_scale'],'weight_numerators':kernel['weight_numerators'],
            'suggestion_point_turns':support['suggestion_point_turns']})
        print('extracted support',i,len(payload),flush=True)
if len(rows)!=29:raise ValueError('Latest 29-support table incomplete')
(dest/'TABLE.json').write_text(json.dumps({'source_sha256':SHA,'supports':rows,
    'note':'Canonical JSON projections of exact support values; source bytes retained unchanged.'},indent=2)+'\n')
print('PASS all 29 physical support values extracted')
