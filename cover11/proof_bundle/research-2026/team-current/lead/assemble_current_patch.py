"""Outward sum current22+constant+local/globalpatch bounds; neverdeclareglobalexclusionwithoutcoverage."""
from pathlib import Path
import json,hashlib
from mpmath import iv
iv.dps=40;P=Path(__file__).parent;f=P/'joint_nested_frozen.json';digest=hashlib.sha256(f.read_bytes()).hexdigest();z=[iv.mpf(f'{x:.9f}')for x in json.loads(f.read_text())['z']]
assert all(x==0 for x in z[50:73]);assert len(z)==121
const=iv.pi*(sum(z[:9])+2*sum(z[9:11])+sum(z[50:71])-2*z[71]-2*z[72])-iv.pi*sum(z[112:])
folder=P.parent/'cline2-coupled-factors'/'out'/('r15_'+digest[:12]);ids=[i for i in range(29)if i not in[1,2,12,13,21,22,23]];summ=iv.mpf(0)
for i in ids:
 paths=list(folder.glob(f'*bound_{i:02d}.json'));assert len(paths)==1,(i,paths)
 d=json.loads(paths[0].read_text());assert d['coefficient_sha256']==digest;summ+=iv.mpf(d['upper'])
local=iv.mpf('28.1044');out={'coefficient_sha256':digest,'constant':str(const),'sum22':str(summ),'constant_plus22':str(const+summ),'local_Q0_total':str(const+summ+local),'local_Q0_strict_below_pi':bool((const+summ+local).b<iv.pi.a),'required_patch_threshold':str(iv.pi-const-summ),'scope':'Q0conditionalonly; globalpatchstillloose'}
for name in ['height_collapsed','cartesian','cartesian_cancel']:
 file=P/f'patch_outer_{name}_certificate.json'
 if file.exists():
  row=json.loads(file.read_text());assert row['coefficient_sha256']==digest;out[name+'_global_total']=str(const+summ+iv.mpf(row['upper']))
(P/'current_patch_assembly.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
