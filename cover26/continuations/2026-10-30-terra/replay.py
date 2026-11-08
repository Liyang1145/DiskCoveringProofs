# SPDX-License-Identifier: MIT
"""Replay the new supplemental inequalities, with explicit scope qualifications."""
from pathlib import Path
from datetime import datetime,timezone
import argparse,hashlib,json,subprocess,sys
HERE=Path(__file__).resolve().parent
def run(rel,args=(),optimized=False):
    cmd=[sys.executable,'-X','utf8']+(['-O'] if optimized else [])+[str(HERE/rel),*map(str,args)]
    p=subprocess.run(cmd,capture_output=True,text=True,encoding='utf8')
    recorded_args=[Path(x).relative_to(HERE).as_posix() if Path(x).is_absolute() else str(x) for x in args]
    return {'path':rel,'arguments':recorded_args,'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr,
            'sha256':hashlib.sha256((HERE/rel).read_bytes()).hexdigest()}
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--report',type=Path);a=ap.parse_args()
    jobs=[('lower/radial_28_125_check.py',()),('audit/independent_28_125_atan.py',()),
      ('lower/radial_9_40_branches.py',('14',)),('lower/radial_9_40_branches.py',('17',)),
      ('audit/independent_9_40_atan.py',('14',)),('audit/independent_9_40_atan.py',('17',)),
      ('lower/verify_reductions.py',()),('audit/verify_boundary_counts.py',()),
      ('geometry/verify_b14.py',()),('geometry/local_obstruction_exact.py',()),
      ('finite-witness/geometry/verify_finite_cover.py',()),('finite-witness/audit/independent_cover23.py',()),
      ('finite-witness/audit/test_exact_masks.py',()),
      ('finite-witness/solver/verify.py',(HERE/'finite-witness/solver/toy_integer_gap.json',HERE/'finite-witness/solver/toy_integer_gap_certificate.json'))]
    results=[]
    for rel,args in jobs:
        result=run(rel,args);results.append(result)
        if result['exit_code']!=0:raise RuntimeError('Replay failed '+rel+': '+result['stderr'])
        print('PASS',rel,*args,flush=True)
    controls=[]
    for rel in ['lower/radial_28_125_check.py','audit/independent_28_125_atan.py','geometry/verify_b14.py']:
        result=run(rel,optimized=True)
        if result['exit_code']==0:raise RuntimeError('Unsafe optimized run accepted')
        controls.append({'path':rel,'control':'python-O-rejected','exit_code':result['exit_code']})
    hashes={p.relative_to(HERE).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
       for p in HERE.rglob('*') if p.is_file() and p.name!='REPLAY.json' and '__pycache__' not in p.parts}
    report={'schema':'n26-second-supplement-replay-v1','client_date':'2026-10-30',
       'execution_clock_utc':datetime.now(timezone.utc).isoformat(),
       'strict_global_lower':'28/125','upper_from_prior_supplement':'234700091/1000000000',
       'fixed_radius_branch_exclusions':{'radius':'9/40','actual_boundary_counts':[14,17],
          'remaining_after_uniform_enlargement':[15,16]},
       'n8_n9_geometry':'published Fejes Toth theorem cited, not freshly reproved',
       'conditional_geometry_interface_replayed':False,'dense_finite_witness_status':'PENDING',
       'exact_optimum_proved':False,'native_formal_payments':0,
       'native_counts_unchanged':[16,4957,344],'fresh_runs':results,'controls':controls,'input_sha256':hashes}
    if a.report:a.report.write_text(json.dumps(report,ensure_ascii=False,indent=2),encoding='utf8')
    print('NEW SUPPLEMENT REPLAY PASSED; exact optimum and native frontier remain open.',flush=True)
if __name__=='__main__':main()
