"""cline2-coupled-factors R15 audit: print the ACTUAL factor list of the certifier as it
binds to the CURRENT frozen coefficients.  Read-only: constructs the interval factor list
and names/domains, then exits WITHOUT running any factor bound.

Run from the repo root (the kernel resolves n11/upper relative to cwd).
"""
import os, sys, json, hashlib
from pathlib import Path
LEAD = Path(__file__).resolve().parents[2] / 'team-current' / 'lead'
ROOT = Path(__file__).resolve().parents[3]
os.chdir(ROOT)
frozen = LEAD / 'joint_nested_frozen.json'
print('frozen file :', frozen.name)
print('sha256      :', hashlib.sha256(frozen.read_bytes()).hexdigest())

# reproduce the certifier's repoint so the factor list binds to the CURRENT coefficients:
# expose the current bytes under the stale name the certifier hardcodes.
alias = LEAD / '_audit_alias'
alias.mkdir(exist_ok=True)
(alias / 'joint_patch_frozen_v2.json').write_bytes(frozen.read_bytes())
import shutil
for s in ['certify_q0_closure.py', 'q0_exact_closure_radius.py', 'q0_graphs.json']:
    shutil.copy2(LEAD / s, alias / s)
(alias / 'n11' / 'upper').mkdir(parents=True, exist_ok=True)
shutil.copy2(ROOT / 'n11' / 'upper' / 'certified_object.json',
             alias / 'n11' / 'upper' / 'certified_object.json')
shutil.copy2(LEAD / 'certify_joint_rest_tight.py', alias / 'certify_joint_rest_tight.py')

src = (LEAD / 'certify_q0_closure.py').read_text()
assert src.count('# Heap entries') == 1
src = src.split('# Heap entries')[0].replace(
    "f'q0_closure_dual_{start}_{span}.json'", "'joint_patch_frozen_v2.json'")
ns = {'__file__': str(alias / 'certify_q0_closure.py')}
sys.argv = ['x', '0', '4']
os.chdir(alias)
exec(src, ns)
factors = ns['factors']
print(f'\nlen(factors) = {len(factors)}  (expect 29)')
print('\nidx | name      | domain (endpoints)')
for i, (name, fun, dom) in enumerate(factors):
    d = [(float(a), float(b)) for a, b in dom]
    print(f'{i:3d} | {name:9s} | {d}')
names = [n for n, _, _ in factors]
print('\nname -> index map:')
for i, n in enumerate(names):
    print(f'   {n:9s} -> {i}')
# the certifier's skip list, and the 22 targets
SKIP = [1, 2, 12, 13, 21, 22, 23]
TO_PROCESS = [i for i in range(29) if i not in SKIP]
print(f'\ncertifier skip list (C854-covered) : {SKIP}')
print(f'the 22 remaining targets          : {TO_PROCESS}')
print(f'count                             : {len(TO_PROCESS)}')
print(f'\nerroneous list used by my driver  : {[i for i in TO_PROCESS if i != 0]}')
print(f'   difference = {{0}} -> factor 0 = "{names[0]}" was wrongly dropped')
# cleanup
shutil.rmtree(alias, ignore_errors=True)
print('\nalias removed')
