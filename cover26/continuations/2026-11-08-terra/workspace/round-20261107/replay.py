"""Fresh, bounded replay of the 2026-11-07 local continuation."""
from pathlib import Path
from datetime import datetime, timezone, timedelta
import hashlib
import json
import platform
import subprocess
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

inputs=list(HERE.glob('*.py'))+list(HERE.glob('*.js'))+list(HERE.glob('*.md'))
inputs.extend(ROOT/p for p in [
    'round-20261030b/area/PROOF.md',
    'round-20261030b/area/FAN-CORRECTION.md',
    'round-20261030b/area/FAN-BOXES.md',
    'round-20261030b/area/verify_fan_boxes.js',
    'round-20261030b/area/verify_fan_correction.js',
    'round-20261030b/audit/AREA-REVIEW.md',
    'round-20261030b/audit/SHARP-EAR-REVIEW.md',
    'construction/rational_voronoi.py',
    'minmaxarena/n26-origin-certificate.json',
])
report={
    'date':datetime.now(timezone(timedelta(hours=8))).isoformat(),
    'platform':platform.platform(),
    'python':sys.version,
    'node':subprocess.check_output(['node','--version'],text=True).strip(),
    'claim':'229/1000 < r_D(26) <= 234700091/1000000000',
    'scope':'bounded exact arithmetic and upper-cover replay; written geometric proof in PROOF.md',
    'inputs':{str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in sorted(set(inputs))},
    'checks':[],
}
checks=[
    ('previous_02285',['node',str(ROOT/'round-20261030b/area/verify_fan_correction.js')],0,None),
    ('previous_02287',['node',str(ROOT/'round-20261030b/area/verify_fan_boxes.js')],0,None),
    ('new_bigint',['node',str(HERE/'verify_shifted_fans.js'),'--write'],0,'PASS: scalar inequalities'),
    ('new_fraction',[sys.executable,str(HERE/'check_independent.py')],0,'"passed": true'),
    ('upper_exact',[sys.executable,str(ROOT/'construction/rational_voronoi.py'),str(ROOT/'minmaxarena/n26-origin-certificate.json')],0,'PASS: 26 rational centers'),
    ('bigint_reject_0230001',['node',str(HERE/'verify_shifted_fans.js'),'--negative-control'],1,'area contradiction 15'),
    ('fraction_reject_0230001',[sys.executable,str(HERE/'check_independent.py'),'--negative-control'],0,'"control": "reject larger radius"'),
]
all_passed=True
for name,command,expected,marker in checks:
    result=subprocess.run(command,cwd=HERE,text=True,capture_output=True,timeout=120)
    passed=result.returncode==expected and (marker is None or marker in result.stdout+result.stderr)
    all_passed=all_passed and passed
    report['checks'].append({'name':name,'command':command,'exit_code':result.returncode,
        'expected_exit_code':expected,'passed':passed,'stdout':result.stdout,'stderr':result.stderr})
    print(name,'PASS' if passed else 'FAIL',flush=True)
report['all_passed']=all_passed
report['certificate_sha256']=sha(HERE/'certificate.json')
report['inputs_unchanged']=all(sha(ROOT/p)==digest for p,digest in report['inputs'].items())
all_passed=all_passed and report['inputs_unchanged']
report['all_passed']=all_passed
(HERE/'REPLAY.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
if not all_passed:
    raise SystemExit('Replay failed; inspect REPLAY.json')
print('PASS: all 7 checks; inputs unchanged')
