"""Instrument the lead module's own closures to see exactly which numbers it uses.

No writes into the lead tree. Importing the module re-runs the whole B&B (its row/span
come from sys.argv), so this script also serves as a same-code replay."
"""
import io, json, math, os, sys
from contextlib import redirect_stdout
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAD = HERE.parent / 'lead'
os.chdir(LEAD)
sys.path.insert(0, str(LEAD))
sys.argv = ['certify_q0_closure.py', '0', '3']

buf = io.StringIO()
with redirect_stdout(buf):
    import certify_q0_closure as C   # module body runs the full B&B; no writes

print('== A. what the module itself reports / stores ==')
print('module total          =', C.total)
print('module result (first 6):')
for r in C.result[:6]:
    print('   ', r)
print('module stdout tail: "CERTIFIED ..." ->', buf.getvalue()[-70:].replace('\n', ' '))

print('\n== B. coefficient-level re-check with the module\'s own symbols ==')
zf9 = [C.iv.mpf(f'{v:.9f}') for v in C.row['z']]
coeff = sum(zf9[:9]) + 2 * sum(zf9[9:11]) + sum(zf9[50:71]) - 2 * zf9[71] - 2 * zf9[72]
print('coeff part * pi      =', coeff * C.pi)
print('2*z[72]*asin(2R)     =', 2 * zf9[72] * C.iv.asin(2 * C.R) if hasattr(C.iv, 'asin')
      else 2 * zf9[72] * C.iv.atan2(2 * C.R, C.iv.sqrt(1 - (2 * C.R) ** 2)))
print('-pi*sum(z[cl:])      =', -C.pi * sum(zf9[112:]))
print('sum stored uppers    =', sum(f['upper'] for f in C.result))

print('\n== C. what the module\'s own switch closures compute vs my formula ==')
z = [float(v) for v in C.row['z']]
faces = [tuple(f) for f in C.faces]
edges = [tuple(e) for e in C.edges]
fam = {n: (f, d) for n, f, d in C.factors}
for bi in range(3):
    f, dom = fam[f'switch{bi}']
    v0 = f([C.iv.mpf(0)])
    i, j = bi, (bi + 1) % 9
    ei = edges.index(tuple(sorted((i, j))))
    mine_c = z[i] + z[j] - z[50 + ei] + 2 * z[112 + bi]
    mine_d = z[11 + ei]
    mine_e = z[32 + 2 * i + 1] + z[32 + 2 * j]
    mine_g = -z[73 + ei]
    mine_h = z[94 + 2 * i + 1] + z[94 + 2 * j]
    print(f'switch{bi}: module f(0) = {v0}')
    print(f'          my c,d,e,g,h = {mine_c:+.9f} {mine_d:+.9f} {mine_e:+.9f} {mine_g:+.9f} {mine_h:+.9f}')
    print(f'          my R(0) = e = {mine_e:+.9f}')

print('\n== D. introspect the switch0 closure arguments (bypasses assumption) ==')
f0, _ = fam['switch0']
import inspect
# recover default arguments captured by the closure
dflts = dict(zip(f0.__code__.co_varnames[-5:], f0.__defaults__ or ()))
for k, v in dflts.items():
    print(f'   default {k} = {v}')

print('\n== E. ring0 closure defaults ==')
r0, _ = fam['ring0']
dfl = dict(zip(r0.__code__.co_varnames[-9:], r0.__defaults__ or ()))
for k, v in dfl.items():
    print(f'   default {k} = {v}')

print('\n== F. face0 closure defaults ==')
fc0, _ = fam['face0']
for k, v in dict(zip(fc0.__code__.co_varnames[-3:], fc0.__defaults__ or ())).items():
    print(f'   default {k} = {v}')
