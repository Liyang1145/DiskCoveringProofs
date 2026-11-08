"""Bounded exact replay of the new geometry interface and native byte receipts."""
from pathlib import Path
from datetime import datetime,timezone,timedelta
import hashlib,json,platform,subprocess,sys
import sympy

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
inputs=list(HERE.glob('*.py'))+list(HERE.glob('*.md'))
inputs+=list((HERE/'native-source').glob('*'))
inputs+=[HERE/'native-recovered/n26-mixed-after-six-midarc-supplemental-current-v1.json',
         ROOT/'audit/native-recovered/cover26/proof_bundle/outputs/n26-mixed-after-six-midarc-independent-final-v1.json',
         ROOT/'round-20261107b/topology.json']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
report={'date':datetime.now(timezone(timedelta(hours=8))).isoformat(),
    'platform':platform.platform(),'python':sys.version,'sympy':sympy.__version__,
    'scope':'exact premises and byte restoration; continuous proof in PROOF.md; no new global radius bound',
    'inputs':{p.relative_to(ROOT).as_posix():sha(p) for p in sorted(set(inputs)) if p.is_file()},'checks':[]}
for name,command,marker in [
    ('geometry_interface',[sys.executable,str(HERE/'verify_interface.py')],'"passed": true'),
    ('reject_wrong_radius_scope',[sys.executable,str(HERE/'verify_interface.py'),'--negative-control'],'out-of-scope threshold rejected'),
    ('native_report_and_sources',[sys.executable,str(HERE/'verify_native_receipts.py')],'PASS original current/final byte identities'),
]:
    result=subprocess.run(command,cwd=HERE,capture_output=True,text=True,timeout=120)
    passed=result.returncode==0 and marker in result.stdout
    report['checks'].append({'name':name,'command':command,'exit_code':result.returncode,
        'passed':passed,'stdout':result.stdout,'stderr':result.stderr})
    print(name,'PASS' if passed else 'FAIL',flush=True)
report['inputs_unchanged']=all(sha(ROOT/name)==value for name,value in report['inputs'].items())
report['all_passed']=report['inputs_unchanged'] and all(row['passed'] for row in report['checks'])
report['outputs']={name:sha(HERE/name) for name in ['INTERFACE-CERTIFICATE.json','NATIVE-RECEIPTS.json']}
(HERE/'REPLAY.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
if not report['all_passed']:raise SystemExit('Replay failed')
print('PASS all 3 checks; inputs unchanged')
