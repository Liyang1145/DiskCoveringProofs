"""Lead's independent final content join; no producer/verifier imports.
Not an independent replay of the integer kernel. Separately audits actual
source-snapshot leaf data, original fresh rows, final rows and pinned hashes.
"""
from pathlib import Path
from fractions import Fraction as Q
import json, hashlib
P=Path(__file__).resolve().parents[1]; M=P/'members/finite-reduction/integer-domain'; O=M/'out'
rawcache={}
def raw(p):
 p=p.resolve()
 if p not in rawcache:rawcache[p]=p.read_bytes()
 return rawcache[p]
def sha(p):return hashlib.sha256(raw(p)).hexdigest()
def doc(p):return json.loads(raw(p))
def rows(p):return [json.loads(s) for s in raw(p).decode('utf8').splitlines() if s.strip()]
def hw(v):return hashlib.sha256(json.dumps(v,sort_keys=True).encode()).hexdigest()
manifest=P/'members/structure/parallel-domain/completed-domain-base.json';D=doc(manifest)
assert sha(manifest)=='7f44132b8dd09c8377b7e300caebe6ca5485b8933bde86455f67062733c1c57a'
assert not D['pending']
leaves=[l for l in D['leaves'] if l['type']=='atomic'];assert len(leaves)==6723
prov=doc(O/'cache-provenance.json');assert prov['failed']==0
assert prov['cache_sha256']==sha(O/'certified-cache.jsonl')
pv={v['ckey']:v for v in prov['verified']};assert len(pv)==len(prov['verified'])==6723
for f,h in prov['row_files_sha256'].items():assert sha(M/f)==h
source={}
for s,entry in prov['snapshot_registry'].items():
 p=P/entry['path'];assert sha(p)==entry['sha256'];source[s]=[l for l in doc(p)['leaves'] if l['type']=='atomic']
k=sha(P/'members/upper-audit/integer-atomic/py/integer_kernel.py');kn=sha(P/'members/upper-audit/integer-atomic/py/integer_kernel_n.py')
vs={2048:sha(P/'evidence/atomic-unit-vectors-2048.json'),8192:sha(P/'members/upper-audit/integer-atomic/evidence/canonical-unit-vectors-8192.json')}
R=rows(O/'verify-completed-domain.jsonl');assert len(R)==6723
assert sorted(r['idx'] for r in R)==list(range(6723))
linecache={};gaps=[];scales={}
for r in R:
 l=leaves[r['idx']];N=l.get('atomN',2048);sc=r['used_scale'];assert sc in (26,28)
 key='N%d:S%d:%s:%s:%s:%s:%s'%(N,sc,vs[N],k,kn,hw(l['H']),hw(l['proposal']['weights']))
 assert r['ckey']==key and r['snapshot']==sha(manifest)
 assert r['n']==N and r['units']==vs[N] and r['kernel']==k and r['kernel_n']==kn
 v=pv[key];sl=source[v['fresh_stem']][v['fresh_idx']]
 assert sl['H']==l['H'] and sl['proposal']['weights']==l['proposal']['weights'] and sl.get('atomN',2048)==N
 f=M/v['fresh_file'];assert sha(f)==v['fresh_file_sha256']
 if f not in linecache:linecache[f]=raw(f).decode('utf8').splitlines()
 fresh=json.loads(linecache[f][v['fresh_line']-1]);assert fresh['idx']==v['fresh_idx']
 assert fresh['snapshot']==prov['snapshot_registry'][v['fresh_stem']]['sha256']
 assert fresh['status']==r['status']=='certified'
 if not v['pre_field_rule']:assert fresh['from_cache'] is False
 else:assert v['fresh_stem']=='stage2200' and N==2048 and sc==26
 assert fresh['units']==vs[N] and fresh['kernel']==k
 if fresh.get('kernel_n') is None:assert v['fresh_stem'] in ('stage2200','stage6700') and N==2048
 else:assert fresh['kernel_n']==kn
 if fresh.get('used_scale') is None:assert sc==26 and v['fresh_stem'] in ('stage2200','stage6700','stage11825')
 else:assert fresh['used_scale']==sc
 for field in ('demand','max_capture','gap'):
  assert isinstance(r[field],int) and r[field]==fresh[field]==v[field]
 assert r['demand']-10*r['max_capture']==r['gap']>0
 gaps.append(r['gap']);scales[sc]=scales.get(sc,0)+1
summary=doc(O/'verify-completed-domain-summary.json');assert summary['snapshot_sha256']==sha(manifest)
assert summary['infeasible']['all_reproduced'] and summary['prune3_vs_radical']['consistent']==187
partition=doc(P/'evidence/completed-domain-prefix-partition.json');assert partition['source_sha256']==sha(manifest) and partition['exact_partition']
fz=doc(O/'freeze-completed-domain.json')
for field,f in [('cache_sha256','certified-cache.jsonl'),('provenance_sha256','cache-provenance.json'),('jsonl_sha256','verify-completed-domain.jsonl'),('summary_sha256','verify-completed-domain-summary.json')]:assert fz[field]==sha(O/f)
out=dict(status='content-join-verified',scope='whole completed-domain manifest; not independent integer replay',atomic=6723,pruned=318,pending=0,minimum_integer_gap=min(gaps),scales=scales,manifest_sha256=sha(manifest),files={str(p.relative_to(P)):hashlib.sha256(b).hexdigest() for p,b in rawcache.items()},legacy='pre-field exceptions restricted to named generation/N/scale; execution call contract separately audited')
(P/'evidence/final-content-audit.json').write_text(json.dumps(out,indent=2),encoding='utf8')
print(json.dumps({k:v for k,v in out.items() if k!='files'}))
