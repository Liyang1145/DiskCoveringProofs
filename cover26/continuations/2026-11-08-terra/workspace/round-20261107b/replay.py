"""Bounded fresh replay: isolated candidate, same-root cover, and lower bound."""
from pathlib import Path
from datetime import datetime,timezone,timedelta
import hashlib,json,subprocess,sys,platform

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
paths=[p for p in HERE.iterdir() if p.suffix in ('.py','.md')]
paths.extend(HERE/name for name in ['root-proposal.json','topology.json','stationary-proposal.json','numerical_contacts.json'])
paths.extend(ROOT/name for name in ['minmaxarena/n26-origin-certificate.json',
    'round-20261107/verify_shifted_fans.js','round-20261107/interval.js','round-20261107/check_independent.py',
    'round-20261107/PROOF.md'])
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
report={'date':datetime.now(timezone(timedelta(hours=8))).isoformat(),
        'platform':platform.platform(),'python':sys.version,
        'claim':'0.229 < r_D(26) <= rho, where rho is the uniquely isolated algebraic root radius',
        'scope':'exact algebraic candidate and attainment; no matching global lower bound',
        'inputs':{p.relative_to(ROOT).as_posix():sha(p) for p in sorted(set(paths))},'checks':[]}
checks=[
    ('root_contraction',[sys.executable,str(HERE/'verify_root.py')],'"passed": true'),
    ('same_root_cover',[sys.executable,str(HERE/'verify_cover.py')],'"global_optimality_proved": false'),
    ('reject_perturbed_box',[sys.executable,str(HERE/'verify_root.py'),'--negative-control'],'perturbed radius rejected'),
    ('reject_shrunk_fixed_cover',[sys.executable,str(HERE/'verify_cover.py'),'--negative-control'],'rho-10^-40 fails'),
    ('previous_lower_bigint',['node',str(ROOT/'round-20261107/verify_shifted_fans.js')],'PASS: scalar inequalities'),
    ('previous_lower_fraction',[sys.executable,str(ROOT/'round-20261107/check_independent.py')],'"passed": true'),
]
for name,command,marker in checks:
    result=subprocess.run(command,cwd=HERE,capture_output=True,text=True,timeout=120)
    passed=result.returncode==0 and marker in result.stdout
    report['checks'].append({'name':name,'command':command,'exit_code':result.returncode,
        'passed':passed,'stdout':result.stdout,'stderr':result.stderr})
    print(name,'PASS' if passed else 'FAIL',flush=True)
report['inputs_unchanged']=all(sha(ROOT/p)==value for p,value in report['inputs'].items())
report['outputs']={name:sha(HERE/name) for name in ['ROOT-CERTIFICATE.json','COVER-CERTIFICATE.json']}
report['all_passed']=report['inputs_unchanged'] and all(c['passed'] for c in report['checks'])
(HERE/'REPLAY.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
if not report['all_passed']:raise SystemExit('Replay failed')
print('PASS: all 6 checks; inputs unchanged')
