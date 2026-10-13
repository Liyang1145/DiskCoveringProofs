"""Disassemble the ACTUAL switch/ring closures of the running module and reverse-engineer
which z-index each captured coefficient comes from.

Rationale: the file text I read appears inconsistent with what the closures compute, so the
audit must rely on the executed code, not on the comment/line structure.
"""
import io, dis, os, sys, json, itertools
from contextlib import redirect_stdout
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAD = HERE.parent / 'lead'
os.chdir(LEAD)
sys.path.insert(0, str(LEAD))
sys.argv = ['certify_q0_closure.py', '0', '3']

src = (LEAD / 'certify_q0_closure.py').read_bytes()
import hashlib
print('certify_q0_closure.py sha256 =', hashlib.sha256(src).hexdigest())
print('size =', len(src), 'bytes')

with redirect_stdout(io.StringIO()):
    import certify_q0_closure as C

zf = [float(v) for v in C.row['z']]

# --- map every possible small-algebraic value of z to its index for identification -----
ident = {}

def reg(val, tag):
    ident.setdefault(round(val, 12), []).append(tag)

for i, v in enumerate(zf):
    reg(v, f'z{i}')
    reg(-v, f'-z{i}')
    reg(2 * v, f'2z{i}')
    reg(-2 * v, f'-2z{i}')
for i in range(len(zf)):
    for j in range(i + 1, len(zf)):
        reg(zf[i] + zf[j], f'z{i}+z{j}')
        reg(zf[i] - zf[j], f'z{i}-z{j}')
        reg(zf[j] - zf[i], f'z{j}-z{i}')
for i in range(len(zf)):
    for j in range(i + 1, len(zf)):
        for k in range(j + 1, len(zf)):
            reg(zf[i] + zf[j] + zf[k], f'z{i}+z{j}+z{k}')
            reg(zf[i] + zf[j] - zf[k], f'z{i}+z{j}-z{k}')
            reg(zf[i] - zf[j] - zf[k], f'z{i}-z{j}-z{k}')

NAMES = {}

def identify(name, val):
    key = round(val, 12)
    hits = ident.get(key, [])
    hits = [h for h in hits if len(h) < 26]     # keep the readable ones
    print(f'  {name:8s} = {val:+.12f}   <- {hits[:4] if hits else "NO MATCH"}')
    NAMES[name] = val

fam = {n: f for n, f, d in C.factors}

print('\n== switch closures: defaults, identified ==')
for bi in [0, 1, 3, 5]:
    f = fam[f'switch{bi}']
    args = dict(zip(f.__code__.co_varnames[-5:], f.__defaults__))
    print(f'switch{bi}:')
    for k, v in args.items():
        try:
            identify(k, float(v.a))
        except Exception as exc:
            print('   ', k, 'unfloatable', exc)

print('\n== ring closures: defaults, identified ==')
for i in [0, 1, 5]:
    f = fam[f'ring{i}']
    args = dict(zip(f.__code__.co_varnames[-9:], f.__defaults__))
    print(f'ring{i}:')
    for k, v in args.items():
        try:
            identify(k, float(v.a))
        except Exception as exc:
            print('   ', k, 'unfloatable', exc)

print('\n== bytecode of switch0 body ==')
f = fam['switch0']
dis.dis(f, depth=0)
print('\n== bytecode of ring0 body (co_consts / names) ==')
r = fam['ring0']
print('consts:', r.__code__.co_consts)
print('names :', r.__code__.co_names)
print('varnames:', r.__code__.co_varnames)
print('freevars:', r.__code__.co_freevars)
print('cellvals:', [cv.cell_contents if not isinstance(cv.cell_contents, type(dis)) else cv.cell_contents
                    for cv in (r.__closure__ or [])][:5])
