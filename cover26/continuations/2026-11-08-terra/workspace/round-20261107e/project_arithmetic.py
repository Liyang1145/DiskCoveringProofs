"""Make a bounded working projection of a hash-verified historical snapshot.

The complete 480 MB source remains unchanged. No old proof is reaccepted here.
"""
from pathlib import Path
import hashlib,json,sys
from decimal import Decimal

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'vendor'))
import ijson
from ijson.common import ObjectBuilder

SOURCE=HERE/'native-recovered/n26-root25-current346-refit2-origin-append-composition-v1.json'
EXPECTED='c1675552b56d762de0bca83ca3adbb28e06c71e95c94b387d7f216eee41187c9'
h=hashlib.sha256()
with SOURCE.open('rb') as source:
    for chunk in iter(lambda:source.read(1024*1024),b''):h.update(chunk)
if h.hexdigest()!=EXPECTED:raise ValueError('Wrong original arithmetic snapshot')

projection={};fields=[];key=None;builder=None;events=0;truncated=False
skip={'arithmetic_ledger','alternative_supports','full134rod_supports','fresh_joint_origin_supports'}
with SOURCE.open('rb') as source:
    for prefix,event,value in ijson.parse(source):
        if prefix=='' and event=='map_key':
            key=value;events=0;truncated=key in skip
            builder=None if truncated else ObjectBuilder()
            continue
        if key is None:continue
        if prefix==key or prefix.startswith(key+'.'):
            events+=1
            if events>600000 and builder is not None:
                builder=None;truncated=True
            if builder is not None:builder.event(event,value)
            if prefix==key and event in {'end_map','end_array','string','number','boolean','null'}:
                if builder is not None:projection[key]=builder.value
                fields.append({'key':key,'events':events,'projected':builder is not None,'deliberately_skipped':truncated})
                print('field',key,'events',events,'projected',builder is not None,flush=True)
                key=None;builder=None

def encode(x):
    if isinstance(x,Decimal):return str(x)
    raise TypeError(type(x).__name__)

(HERE/'arithmetic-working-projection.json').write_text(json.dumps(projection,indent=2,default=encode)+'\n')
receipt={'source_sha256':EXPECTED,'source_bytes':SOURCE.stat().st_size,
    'parser':'ijson '+ijson.__version__,'parser_backend':ijson.backend,
    'fields':fields,'projection_is_not_complete_snapshot':True,
    'historical_arithmetic_ledger_replayed':False,'new_geometric_payments':0}
(HERE/'PROJECTION-RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS complete source parsed; bounded projection saved without old arithmetic acceptance')
