from pathlib import Path
import json,hashlib
from mpmath import iv
P=Path(__file__).parent;iv.dps=45;frozen=P/'middle_inward_frozen.json';digest=hashlib.sha256(frozen.read_bytes()).hexdigest();j=json.loads(frozen.read_text());z=[iv.mpf(f'{x:.9f}')for x in j['z']];pi=iv.pi
rows=[]
for i in range(29):
 p=P/f'middle_inward_bound_{i:02d}.json'
 if not p.exists():print('MISSING',i);continue
 r=json.loads(p.read_text());assert r['coefficient_sha256']==digest and r['factor_index']==i;rows.append(r)
if len(rows)<29:raise SystemExit('Incomplete: no conclusion')
assert all(z[k].a>=0 for k in range(50,73));assert z[72]==0
constant=pi*(sum(z[:9])+2*sum(z[9:11])+sum(z[50:71])-2*z[71])-pi*sum(z[112:]);total=constant+sum(iv.mpf(r['upper']) for r in rows)
out={'scope':'conditional alpha2=pi in actual inward q0k4 covers r in[3/8,37999/100000]; C844 constraints imposed as safe intervalfilter on everyothersector','total':str(total),'pi':str(pi),'strict':bool(total.b<pi.a),'coefficient_sha256':digest,'factors':rows}
(P/'middle_inward_assembled.json').write_text(json.dumps(out,indent=2));print(out['total'],'strict',out['strict']);assert out['strict']
