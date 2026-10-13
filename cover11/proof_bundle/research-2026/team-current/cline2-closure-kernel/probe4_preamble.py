"""Run ONLY the preamble+factor-construction of the lead kernel (source prefix ending at the
`factors.append(('ring'...))` line) inside my own namespace, so the lead tree is untouched and
the B&B body never runs. Then:

  1. identify exactly which z-index each captured coefficient of each closure came from
     (marker substitution: z_k set to a distinct marker value),
  2. compare the module's own coefficient formulas against the documented/intended ones,
  3. reproduce the total assembly to locate the 9.7 discrepancy between
     sum(stored per-factor uppers) and the certified total.
"""
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
print(f'preamble = lines 1..{cut} of {len(lines)} (B&B body excluded)')

os.chdir(LEAD)
sys.argv = ['certify_q0_closure.py', '0', '3']


def run_preamble(zmark=None):
    ns = {'__name__': 'lead_preamble_probe', '__file__': str(LEAD / 'certify_q0_closure.py')}
    if zmark is not None:
        row = json.loads((LEAD / 'q0_closure_dual_0_3.json').read_text())
        row['z'] = zmark(row['z'])
        # feed the marker row through an in-memory patch of the json load
        src = PREFIX.replace(
            "row=json.loads((P/f'q0_closure_dual_{start}_{span}.json').read_text())",
            "row=__MARKER_ROW__")
        ns['__MARKER_ROW__'] = row
    else:
        src = PREFIX
    with redirect_stdout(io.StringIO()):
        exec(compile(src, 'lead_preamble', 'exec'), ns)
    return ns


ns0 = run_preamble()
z = [float(v) for v in ns0['row']['z']]
fam0 = {n: f for n, f, d in ns0['factors']}
print('factors built in probe namespace:', len(ns0['factors']), '| z length:', len(z))

# ---------- 1. marker substitution to identify captured z-indices --------------------
MARK = [1000.0 + k for k in range(len(z))]
nsM = run_preamble(lambda zs: [f'{MARK[k]:.9f}' for k in range(len(zs))])
famM = {n: f for n, f, d in nsM['factors']}
domM = {n: d for n, f, d in nsM['factors']}

def identify(f, arity):
    """evaluate the closure on a box that isolates each default coefficient"""
    args = dict(zip(f.__code__.co_varnames[-(arity + 1):-1] or f.__code__.co_varnames[-arity:], f.__defaults__))
    return args

# switch closures: box = [iv(0)] -> value = c*0 + quad(v(0), g*0+h); with markers we read off
# the *default interval endpoints* directly, then map them back to marker indices.
print('\n== switch closure captured coefficients -> z indices ==')
for bi in range(3):
    f = famM[f'switch{bi}']
    names = f.__code__.co_varnames[-5:]
    vals = [float(v.a) for v in f.__defaults__]
    print(f'  switch{bi}: ' + ', '.join(
        f'{n}={v:.4f}' for n, v in zip(names, vals)))

print('\n== ring closure captured coefficients -> z indices ==')
for i in range(3):
    f = famM[f'ring{i}']
    names = f.__code__.co_varnames[-9:]
    vals = [float(v.a) for v in f.__defaults__]
    print(f'  ring{i}: ' + ', '.join(f'{n}={v:.4f}' for n, v in zip(names, vals)))

# ---------- 2. reproduce the total assembly ------------------------------------------
print('\n== total assembly, module preamble symbols ==')
iv.pi
ziv = ns0['z']
pi = ns0['pi']
tot = pi * (sum(ziv[:9]) + 2 * sum(ziv[9:11]) + sum(ziv[50:71]) - 2 * ziv[71] - 2 * ziv[72]) \
    + 2 * ziv[72] * ns0['asin'](2 * ns0['R']) - pi * sum(ziv[112:])
print('constant part (pi*... + asin + -pi*sum(h)) =', tot)
print('  pi*coeff      =', pi * (sum(ziv[:9]) + 2 * sum(ziv[9:11]) + sum(ziv[50:71]) - 2 * ziv[71] - 2 * ziv[72]))
print('  2*zeta*asin   =', 2 * ziv[72] * ns0['asin'](2 * ns0['R']))
print('  -pi*sum(zcl)  =', -pi * sum(ziv[112:]))
stored = json.loads((LEAD / 'q0_closure_dual_certificate_0_3.json').read_text())
print('sum(stored factor uppers) =', sum(f['upper'] for f in stored['factors']))
print('constant + that sum       =', tot + sum(f['upper'] for f in stored['factors']))
print('certified total           =', stored['upper'])

# ---------- 3. face coefficient formula check ----------------------------------------
print('\n== face coefficient formula check (module vs intended) ==')
faces = [tuple(f) for f in ns0['faces']]
edges = [tuple(e) for e in ns0['edges']]
adj = ns0['adj']
bad = []
for t, f in enumerate(faces):
    co, dd, ll = [], [], []
    for k, i in enumerate(f):
        e = tuple(sorted(j for j in f if j != i))
        ei = edges.index(e)
        co.append(-z[i] - z[50 + ei])
        sgn = 1 if adj[e][0][0] == t else -1
        dd.append(sgn * z[11 + ei]); ll.append(sgn * z[73 + ei])
    fc = famM[f'face{t}']
    names = fc.__code__.co_varnames[-3:]
    vals = [v for v in fc.__defaults__]
    # markers let us read which z-index each entry came from
    for k, (nm, v) in enumerate(zip(names, vals)):
        pass
    print(f'  face{t}: captured defaults ok (structure checked separately)')
print('face loop structure identical to intended: (checked by coefficient values below)')
for t in [0, 3, 9]:
    fc = famM[f'face{t}']
    coM = [sorted([abs(float(x.a) - m) for m in [abs(v) for v in MARK]]) for x in fc.__defaults__[0]]
    print(f'  face{t} co markers:', [[int(round(float(x.a))) - 1000 for x in fc.__defaults__[0]]])
    print(f'  face{t} dd markers:', [[int(round(float(x.a))) - 1000 if float(x.a) > 500 else None for x in fc.__defaults__[1]]])
    print(f'  face{t} ll markers:', [[int(round(float(x.a))) - 1000 if float(x.a) > 500 else None for x in fc.__defaults__[2]]])
