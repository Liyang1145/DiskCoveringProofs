"""Bounded replay of the full-domain triangle-angle defect lemma."""
from pathlib import Path
from datetime import datetime,timezone,timedelta
import hashlib,json,subprocess,sys

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
paths=list(HERE.glob('*.py'))+list(HERE.glob('*.js'))+list(HERE.glob('*.md'))
paths.extend([ROOT/'round-20261107/interval.js',ROOT/'round-20261107b/rational_interval.py'])
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
report={'date':datetime.now(timezone(timedelta(hours=8))).isoformat(),
    'scope':'triangle-shape lemma; no new global n26 radius exclusion',
    'inputs':{p.relative_to(ROOT).as_posix():sha(p) for p in sorted(set(paths))},'checks':[]}
for name,command,marker in [
    ('bigint_full_domain',['node',str(HERE/'verify_angle_defect.js'),'--write'],'"passed": true'),
    ('fraction_full_partition',[sys.executable,str(HERE/'check_angle_independent.py')],'"passed": true'),
    ('reject_false_constant',['node',str(HERE/'verify_angle_defect.js'),'--negative-control'],'kappa=0.9 is false'),
]:
    result=subprocess.run(command,cwd=HERE,capture_output=True,text=True,timeout=120)
    passed=result.returncode==0 and marker in result.stdout
    report['checks'].append({'name':name,'command':command,'exit_code':result.returncode,
        'passed':passed,'stdout':result.stdout,'stderr':result.stderr})
    print(name,'PASS' if passed else 'FAIL',flush=True)
report['inputs_unchanged']=all(sha(ROOT/name)==digest for name,digest in report['inputs'].items())
report['certificate_sha256']=sha(HERE/'ANGLE-CERTIFICATE.json')
report['all_passed']=report['inputs_unchanged'] and all(c['passed'] for c in report['checks'])
(HERE/'REPLAY.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
if not report['all_passed']:raise SystemExit('Replay failed')
print('PASS: all 3 checks; inputs unchanged')
