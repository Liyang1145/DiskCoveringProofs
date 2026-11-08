"""Project an already-complete mask family to a specified subset of points.
Completeness is inherited only if the source family was proved complete.
"""
import argparse,gzip,hashlib,json
from pathlib import Path
if not __debug__:raise RuntimeError('Assertions must be enabled')
ap=argparse.ArgumentParser();ap.add_argument('source');ap.add_argument('destination');ap.add_argument('--indices',help='JSON list of distinct source indices');ap.add_argument('--count',type=int,default=400);args=ap.parse_args()
raw=Path(args.source).read_bytes();d=json.loads(gzip.decompress(raw) if raw[:2]==b'\x1f\x8b' else raw);n=len(d['points']);assert n>0
if args.indices:
 ind=json.loads(Path(args.indices).read_text(encoding='utf8'));assert isinstance(ind,list)
else:
 assert 0<args.count<=n
 ind=[j*n//args.count for j in range(args.count)]
assert len(ind)==len(set(ind)) and all(type(i)is int and 0<=i<n for i in ind)
masks=set()
for v in d['masks']:
 m=int(v,16);assert m>=0 and m>>n==0
 z=sum(((m>>i)&1)<<j for j,i in enumerate(ind))
 if z:masks.add(z)
out={'radius':d.get('radius'),'points':[d['points'][i] for i in ind],'masks':[hex(v) for v in sorted(masks)],'source_sha256':hashlib.sha256(raw).hexdigest(),'source_indices':ind,'geometry_scope':'Projection preserves a source family covering all realizable masks; it does not prove that source property. Values may be over-approximations.'}
Path(args.destination).write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8')
print('source points',n,'selected',len(ind),'unique projected masks',len(masks),'source SHA',out['source_sha256'])
