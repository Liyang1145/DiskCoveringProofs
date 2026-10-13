"""Exhaustive identification: match each captured switch/ring parameter value against every
single/double/signed combination of z entries. Removes all guesswork about which z-index the
running code actually reads."""
import io, os, sys, itertools
from contextlib import redirect_stdout
from pathlib import Path

LEAD = Path(__file__).resolve().parents[1] / 'lead'
os.chdir(LEAD)
sys.path.insert(0, str(LEAD))
sys.argv = ['certify_q0_closure.py', '0', '3']
SRC = (LEAD / 'certify_q0_closure.py').read_text().splitlines(keepends=True)
ns = {'__name__': 'iso', '__file__': str(LEAD / 'certify_q0_closure.py')}
with redirect_stdout(io.StringIO()):
    exec(compile(''.join(SRC[:108]), 'iso', 'exec'), ns)

z = ns['z']
zr = [round(float(v.a), 9) for v in z]


def fmt(sets):
    out = []
    for s in sets:
        coeffs = {}
        for c, i in s:
            coeffs[i] = coeffs.get(i, 0) + c
        terms = []
        for i, c in sorted(coeffs.items()):
            if c == 0:
                continue
            terms.append(('' if c == 1 else '-' if c == -1 else f'{c}') + f'z{i}')
        out.append('+'.join(terms) if terms else '0')
    return out


def match(val, maxterms=3):
    """find all small linear combos of z equal to val"""
    v = round(val, 9)
    hits = []
    for i, zi in enumerate(zr):
        if abs(zi - v) < 5e-10:
            hits.append([(1, i)])
    for i, j in itertools.combinations(range(len(zr)), 2):
        s = zr[i] + zr[j]
        if abs(s - v) < 5e-10:
            hits.append([(1, i), (1, j)])
        d = zr[i] - zr[j]
        if abs(d - v) < 5e-10:
            hits.append([(1, i), (-1, j)])
        if abs(-d - v) < 5e-10:
            hits.append([(-1, i), (1, j)])
    for i in range(len(zr)):
        if abs(2 * zr[i] - v) < 5e-10:
            hits.append([(2, i)])
        if abs(-2 * zr[i] - v) < 5e-10:
            hits.append([(-2, i)])
    return hits


fams = {n: (f, d) for n, f, d in ns['factors']}
print('== switch closures ==')
for bi in range(9):
    f, _ = fams[f'switch{bi}']
    names = f.__code__.co_varnames[-5:]
    vals = [float(v.a) for v in f.__defaults__]
    print(f'switch{bi}: ' + '  '.join(
        f'{n}={v:+.9f}[{"|".join(fmt(match(v))[:60])}]' for n, v in zip(names, vals)))

print('\n== ring closures ==')
for i in range(9):
    f, _ = fams[f'ring{i}']
    names = f.__code__.co_varnames[-9:]
    vals = [float(v.a) for v in f.__defaults__]
    print(f'ring{i}:')
    for n, v in zip(names, vals):
        print(f'    {n:8s} = {v:+.9f}   {" | ".join(fmt(match(v))[:110])}')
