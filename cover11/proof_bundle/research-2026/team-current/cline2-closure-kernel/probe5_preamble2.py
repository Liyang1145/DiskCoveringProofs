"""Preamble execution probe v2 (see probe4). Marker substitution with float markers, plus a
LOONAMES analysis of which captured variable each closure actually reads."""
import dis
import io, json, math, os, sys
from contextlib import redirect_stdout
from pathlib import Path
from mpmath import iv

HERE = Path(__file__).resolve().parent
LEAD = HERE.parent / 'lead'
SRC = (LEAD / 'certify_q0_closure.py').read_text()
lines = SRC.splitlines(keepends=True)
cut = next(i for i, L in enumerate(lines) if "factors.append(('ring'" in L) + 1
PREFIX = ''.join(lines[:cut])
print(f'preamble = lines 1..{cut} of {len(lines)}')

os.chdir(LEAD)
sys.argv = ['certify_q0_closure.py', '0', '3']


def run_preamble(marker=False):
    ns = {'__name__': 'lead_preamble_probe', '__file__': str(LEAD / 'certify_q0_closure.py')}
    src = PREFIX
    if marker:
        row = json.loads((LEAD / 'q0_closure_dual_0_3.json').read_text())
        row['z'] = [1000.0 + k + 0.5 for k in range(len(row['z']))]
        row['z'][72] = 0.0                      # keep the module's own z[eta]==0 assertion
        src = PREFIX.replace(
            "row=json.loads((P/f'q0_closure_dual_{start}_{span}.json').read_text())",
            "row=__MARKER_ROW__")
        ns['__MARKER_ROW__'] = row
        src = src.replace("assert z[eta]==0", "pass")
    with redirect_stdout(io.StringIO()):
        exec(compile(src, 'lead_preamble', 'exec'), ns)
    return ns


ns0 = run_preamble()
z = ns0['row']['z']
fam0 = {n: f for n, f, d in ns0['factors']}
print('factors:', len(ns0['factors']), '| z length:', len(z))

MARK = [1000.0 + k + 0.5 for k in range(len(z))]
nsM = run_preamble(marker=True)
famM = {n: f for n, f, d in nsM['factors']}


def dec(v):
    """marker value -> z index (markers are k+1000.5; signs flip on sign-flipped load)"""
    try:
        f = float(v.a)
    except Exception:
        return None
    k = round(abs(f) - 1000.5)
    if k < 0 or k >= len(z) or abs(abs(f) - (1000.5 + k)) > 1e-6:
        return None
    return k if f > 0 else -k - 1        # encode sign into the index label


def codes(f):
    return [i.opname for i in dis.get_instructions(f)]


print('\n== switch closures: which z-index each captured coefficient is ==')
for bi in range(9):
    f = famM[f'switch{bi}']
    names = f.__code__.co_varnames[-5:]
    vals = list(f.__defaults__)
    got = [dec(v) for v in vals]
    print(f'  switch{bi}: ' + ', '.join(f'{n}={g}' for n, g in zip(names, got)))

print('\n== ring closures: which z-index each captured coefficient is ==')
for i in range(9):
    f = famM[f'ring{i}']
    names = f.__code__.co_varnames[-9:]
    vals = list(f.__defaults__)
    got = [dec(v) for v in vals]
    print(f'  ring{i}: ' + ', '.join(f'{n}={g}' for n, g in zip(names, got)))

print('\n== face closures: captured co/dd/ll z-indices ==')
for t in [0, 1, 2, 3, 9, 10]:
    fc = famM[f'face{t}']
    co, dd, ll = fc.__defaults__
    print(f'  face{t} co: {[dec(v) for v in co]}')
    print(f'  face{t} dd: {[dec(v) for v in dd]}')
    print(f'  face{t} ll: {[dec(v) for v in ll]}')

print('\n== LOAD_FAST names per closure (which parameters are actually read) ==')
for name in ['switch0', 'switch5', 'ring0', 'ring4', 'face0']:
    f = fam0[name]
    used = [i.argval for i in dis.get_instructions(f) if i.opname in ('LOAD_FAST', 'LOAD_FAST_BORROW')]
    print(f'  {name}: locals={f.__code__.co_varnames} read={sorted(set(used))}')

print('\n== total assembly (module preamble symbols) ==')
ziv, pi, R_ = ns0['z'], ns0['pi'], ns0['R']
coeff = sum(ziv[:9]) + 2 * sum(ziv[9:11]) + sum(ziv[50:71]) - 2 * ziv[71] - 2 * ziv[72]
const = pi * coeff + 2 * ziv[72] * ns0['asin'](2 * R_) - pi * sum(ziv[112:])
print('pi*coeff     =', pi * coeff)
print('2*zeta*asin  =', 2 * ziv[72] * ns0['asin'](2 * R_))
print('-pi*sum(zcl) =', -pi * sum(ziv[112:]))
print('constant part=', const)
stored = json.loads((LEAD / 'q0_closure_dual_certificate_0_3.json').read_text())
sup = sum(f['upper'] for f in stored['factors'])
print('sum stored uppers =', sup)
print('constant + uppers =', const + sup)
print('certified total   =', stored['upper'])
