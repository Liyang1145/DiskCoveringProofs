"""Replay exact algebraic-point coverage of a fixed rational construction.
No optimizer output is assumed valid; every extremal candidate is re-tested.
"""
import importlib.util,json,hashlib
from pathlib import Path
from fractions import Fraction as F
P=Path(__file__).resolve().parents[1]
source=P/'lead/improved-upper-test.json'
kernel=P/'members/upper/py/repro_c411_independent.py'
s=importlib.util.spec_from_file_location('upper',kernel);M=importlib.util.module_from_spec(s);s.loader.exec_module(M)
j=json.loads(source.read_text());C=[tuple(map(F,c))for c in j['centers']];T=F(j['threshold'])
assert T==F('0.3317320342762341226')
cs=M.candidates(C);bad=[lab for lab,p in cs if not M.covered(p,C,T*T)]
out={'scope':'exact rational configuration upper bound only','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'kernel_sha256':hashlib.sha256(kernel.read_bytes()).hexdigest(),'threshold':str(T),'candidate_count':len(cs),'uncovered':bad,'certified_by_program':not bad}
(P/'lead/improved-upper-replay.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
assert not bad
