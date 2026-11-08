# SPDX-License-Identifier: MIT
"""Freshly replay only the supplemental bounds; never claim exact optimality."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,uuid
from datetime import datetime,timezone

HERE=Path(__file__).resolve().parent
def run(path,args=(),optimized=False):
    command=[sys.executable,'-X','utf8']+(['-O'] if optimized else [])+[str(path),*map(str,args)]
    p=subprocess.run(command,capture_output=True,text=True,encoding='utf8')
    return {'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--report',type=Path);a=parser.parse_args()
    results=[]
    jobs=[('lower/radial_certificate_2_9.py',()),('lower/independent_atan_2_9.py',()),
          ('upper/rational_voronoi.py',(HERE/'upper/n26-origin-certificate.json',)),
          ('upper/verify_triangles.py',()),('upper/minmax_negative.py',()),
          ('boundary14/b14_boundary_norms.py',()),('boundary14/lens_b14_failure.py',())]
    for rel,args in jobs:
        result=run(HERE/rel,args)
        result.update({'path':rel,'sha256':hashlib.sha256((HERE/rel).read_bytes()).hexdigest()})
        results.append(result)
        if result['exit_code']!=0:raise RuntimeError('Replay failed '+rel+': '+result['stderr'])
        print('PASS',rel)
    controls=[]
    for rel in ['lower/radial_certificate_2_9.py','lower/independent_atan_2_9.py','upper/verify_triangles.py']:
        result=run(HERE/rel,optimized=True)
        if result['exit_code']==0:raise RuntimeError('Assertions-disabled run accepted '+rel)
        controls.append({'control':'reject-python-O','path':rel,'exit_code':result['exit_code']})
    p=HERE/('negative-control-'+uuid.uuid4().hex+'.json')
    if not p.resolve().is_relative_to(HERE.resolve()):raise RuntimeError('Unsafe temporary path')
    try:
        data=json.loads((HERE/'upper/n26-origin-certificate.json').read_text(encoding='utf8'))
        data['radius']='0.234700090'
        with p.open('x',encoding='utf8') as stream:json.dump(data,stream)
        result=run(HERE/'upper/rational_voronoi.py',(p,))
        if result['exit_code']==0 or 'Uncovered interior Voronoi vertex' not in result['stderr']:
            raise RuntimeError('Smaller-radius negative control did not fail correctly')
        controls.append({'control':'same-centers-smaller-radius-rejected','exit_code':result['exit_code']})
    finally:
        if p.exists():p.unlink()
    report={'schema':'n26-supplemental-bound-replay-v1','executed_at':datetime.now(timezone.utc).isoformat(),
            'accepted_scope':'2/9 < r_D(26) <= 234700091/1000000000',
            'global_optimality_proved':False,'native_formal_payments':0,
            'native_formal_roots_pending':16,'native_same_root_prefixes_pending':4957,
            'native_arithmetic_open_domains':344,'fresh_runs':results,'rejection_controls':controls}
    if a.report:
        a.report.parent.mkdir(parents=True,exist_ok=True)
        a.report.write_text(json.dumps(report,ensure_ascii=False,indent=2),encoding='utf8')
    print('SUPPLEMENTAL BOUNDS REPLAY PASSED; exact n=26 optimum remains unproved.')
if __name__=='__main__':main()
