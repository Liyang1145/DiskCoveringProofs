"""Bind prior199 exclusions plus newlycompleted76; no premise upgrade from numeric."""
from pathlib import Path
from fractions import Fraction as F
import json,hashlib
P=Path(__file__).resolve().parent
prev=P/'q11-partition-round-retained.json';a=json.loads(prev.read_text());assert a['retained']==[{'family':'10/4','index':879},{'family':'11/3','index':76}]
for name,h in a['source_sha256'].items():assert hashlib.sha256((P/name).read_bytes()).hexdigest()==h
cp=P/'q11-partition-coverage-audit-76.json';c=json.loads(cp.read_text());assert c['status']=='complete_sourcebound_polytope_partition_exclusion'and c['index']==76 and F(c['minimum_lower_exact'])>F('.33173203427623414')
for name,h in c['sources'].items():assert hashlib.sha256((P/name).read_bytes()).hexdigest()==h
out={'status':'necessary_catalogue_single_q10_graph_type','retained':[{'family':'10/4','index':879}],'new_exclusion':{'family':'11/3','index':76},'minimum_new_lower':c['minimum_lower_exact'],'sources':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in [prev,cp]},'scope':'arbitrary14centerunitdiskcovers r<=U; graphuniquenessnotmetricuniqueness'}
(P/'q10-only-879-retained.json').write_text(json.dumps(out,indent=2));print('ONE TYPE REMAINS',out['retained'])
