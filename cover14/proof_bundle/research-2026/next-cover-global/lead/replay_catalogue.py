import importlib.util,json,time
from pathlib import Path
P=Path(__file__).resolve().parents[1]
s=importlib.util.spec_from_file_location('gen',P/'members/topology/gen_k10_catalogue.py');g=importlib.util.module_from_spec(s);s.loader.exec_module(g)
cat=json.loads((P/'members/topology/k-catalogue-n14.json').read_text());out={}
for m in(3,4):
 counts,p1,p2,result,dt=g.run(10,m,budget_s=10000)
 expected={tuple(sorted(tuple(sorted(f))for f in e['faces']))for e in cat[f'10/{m}']}
 assert set(result)==expected
 out[str(m)]={'skeleton_counts':counts,'phase1':p1,'stored_distinct_keys':p2,'runtime':dt,'set_equal':True,'budget_seconds':10000}
(P/'lead/catalogue-full-replay.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
