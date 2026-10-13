"""Finalize this bounded round only: no new partition proposals; revalidate all completedtrees and union."""
from pathlib import Path
from fractions import Fraction as F
import json,hashlib,subprocess,sys,collections
P=Path(__file__).resolve().parent
prev=P/'q10-single-type-retained.json';original=json.loads(prev.read_text())['retained'];ex=[];pending=[];sources={prev.name:hashlib.sha256(prev.read_bytes()).hexdigest()}
for r in original:
 if r['family']!='11/3':continue
 idx=r['index'];tree=P/f'q11-polytope-partition-{idx}.json'
 if not tree.exists():pending.append({'index':idx,'reason':'unstarted'});continue
 a=json.loads(tree.read_text())
 if a['pending']:pending.append({'index':idx,'reason':'bounded_node_limit','pending_nodes':a['pending']});continue
 clip=P/f'q11-split-inductive-audit-{idx}.json'
 if not clip.exists()or json.loads(clip.read_text())['source_sha256']!=hashlib.sha256(tree.read_bytes()).hexdigest():subprocess.run([sys.executable,'-B',str(P/'q11_split_inductive_audit.py'),str(idx)],check=True)
 subprocess.run([sys.executable,'-B',str(P/'q11_partition_coverage_audit.py'),str(idx)],check=True)
 cert=P/f'q11-partition-coverage-audit-{idx}.json';c=json.loads(cert.read_text());assert c['status']=='complete_sourcebound_polytope_partition_exclusion'and c['index']==idx;assert F(c['minimum_lower_exact'])>F('.33173203427623414')
 for name,h in c['sources'].items():assert hashlib.sha256((P/name).read_bytes()).hexdigest()==h
 sources[cert.name]=hashlib.sha256(cert.read_bytes()).hexdigest();ex.append({'family':'11/3','index':idx,'nodes':c['nodes'],'leaves':c['leaves'],'lower_exact':c['minimum_lower_exact']})
removed={r['index']for r in ex};ret=[r for r in original if not(r['family']=='11/3'and r['index']in removed)];out={'status':'necessary_catalogue_after_bounded_q11_partition_round','source_sha256':sources,'excluded_count':len(ex),'remaining_count':len(ret),'counts':dict(collections.Counter(r['family']for r in ret)),'minimum_lower_exact':str(min(F(r['lower_exact'])for r in ex))if ex else None,'exclusions':ex,'unfinished':pending,'retained':ret};(P/'q11-partition-round-retained.json').write_text(json.dumps(out,indent=2));print('FINALROUND',len(ex),'excluded;',len(ret),'remain',out['counts'],flush=True)
