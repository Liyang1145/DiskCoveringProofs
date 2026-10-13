"""Empirical dependency map: for each of the 9 switch, 9 ring and 11 face closures, evaluate it
with one z_k perturbed at a time and record d(closure)/d(z_k).

The factors are linear in whichever z they read, so each column identifies exactly which
z-indices the RUNNING code consumes. Compared afterwards against the intended formulas.
"""
import io, os, sys, json
from contextlib import redirect_stdout
from pathlib import Path

LEAD = Path(__file__).resolve().parents[1] / 'lead'
os.chdir(LEAD)
sys.path.insert(0, str(LEAD))
sys.argv = ['certify_q0_closure.py', '0', '3']

SRC = (LEAD / 'certify_q0_closure.py').read_text().splitlines(keepends=True)
PRE = ''.join(SRC[:108])


def build(zvec):
    row = json.loads((LEAD / 'q0_closure_dual_0_3.json').read_text())
    row['z'] = list(zvec)
    ns = {'__name__': 'iso', '__file__': str(LEAD / 'certify_q0_closure.py'), 'MARKROW': row}
    src = PRE.replace(
        "row=json.loads((P/f'q0_closure_dual_{start}_{span}.json').read_text())", "row=MARKROW")
    with redirect_stdout(io.StringIO()):
        exec(compile(src, 'iso', 'exec'), ns)
    return {(n): f for n, f, d in ns['factors']}, ns


base = json.loads((LEAD / 'q0_closure_dual_0_3.json').read_text())['z']
fam, ns = build(base)
print('built', len(fam), 'factors')
print('co_varnames switch0:', fam['switch0'].__code__.co_varnames)
print('co_varnames ring0  :', fam['ring0'].__code__.co_varnames)
print('co_consts switch0  :', [c for c in fam['switch0'].__code__.co_consts if not isinstance(c, tuple)])
import dis
print('\nswitch0 instructions (opname/argval):')
for ins in dis.get_instructions(fam['switch0']):
    if ins.opname.startswith('LOAD_'):
        print('   ', ins.opname, ins.argval)
print('\nring0 instructions loading closure names:')
for ins in dis.get_instructions(fam['ring0']):
    if ins.opname.startswith('LOAD_') and not ins.opname.startswith('LOAD_GLOBAL'):
        print('   ', ins.opname, ins.argval)
