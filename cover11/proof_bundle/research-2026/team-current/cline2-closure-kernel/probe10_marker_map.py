"""Definitive parameter->z-index map: run the preamble on a marker row z_k = k + 0.375 and read
the captured defaults. Because every captured expression is a signed sum of at most two such
markers, the sum decimals identify the indices exactly."""
import io, json, os, sys, math
from contextlib import redirect_stdout
from pathlib import Path

LEAD = Path(__file__).resolve().parents[1] / 'lead'
os.chdir(LEAD)
sys.path.insert(0, str(LEAD))
sys.argv = ['certify_q0_closure.py', '0', '3']
SRC = (LEAD / 'certify_q0_closure.py').read_text().splitlines(keepends=True)
PRE = ''.join(SRC[:108])

NZ = 121
MARK = [k + 0.375 for k in range(NZ)]
row = {'z': MARK, 'faces': None, 'edges': None}
row0 = json.loads((LEAD / 'q0_closure_dual_0_3.json').read_text())
row['faces'] = row0['faces']
row['edges'] = row0['edges']
row['z'][72] = 0.0                    # keep z[eta]==0 assertion alive

ns = {'__name__': 'iso', '__file__': str(LEAD / 'certify_q0_closure.py'), 'MARKROW': row}
src = PRE.replace("row=json.loads((P/f'q0_closure_dual_{start}_{span}.json').read_text())",
                  "row=MARKROW").replace("assert z[eta]==0", "pass")
with redirect_stdout(io.StringIO()):
    exec(compile(src, 'iso', 'exec'), ns)


def dec(a, b):
    """marker interval -> symbolic expression string"""
    def one(v):
        k = float(v) - 0.375
        ki = int(math.floor(k + 0.5))
        if abs(k - ki) > 1e-5:
            return f'?{float(v)}'
        return f'z{ki}'
    sa, sb = one(a), one(b)
    return sa if sa == sb else f'{sa}..{sb}'


fams = [(n, f, d) for n, f, d in ns['factors']]
print('=== FACE closure captured (co, dd, ll) ===')
for n, f, d in fams[:11]:
    co, dd, ll = f.__defaults__
    print(f'{n:8s} co=[{", ".join(dec(v.a, v.b) for v in co)}]')
    print(f'{"":8s} dd=[{", ".join(dec(v.a, v.b) for v in dd)}]')
    print(f'{"":8s} ll=[{", ".join(dec(v.a, v.b) for v in ll)}]')

print('\n=== SWITCH closure captured (c, d, e, g, h) ===')
for n, f, d in fams[11:20]:
    names = f.__code__.co_varnames[-5:]
    print(f'{n:8s} ' + '  '.join(f'{nm}={dec(v.a, v.b)}' for nm, v in zip(names, f.__defaults__)))

print('\n=== RING closure captured (mu, d, e, C, dl, el, hl, hr) ===')
for n, f, d in fams[20:29]:
    names = f.__code__.co_varnames[-9:-1]
    print(f'{n:8s} ' + '  '.join(f'{nm}={dec(v.a, v.b)}' for nm, v in zip(names, f.__defaults__)))

print('\n=== module constants ===')
for k in ['side', 'rr', 'kap', 'lam', 'eta', 'lin', 'cl', 'span']:
    print(f'  {k} = {ns[k]}')

