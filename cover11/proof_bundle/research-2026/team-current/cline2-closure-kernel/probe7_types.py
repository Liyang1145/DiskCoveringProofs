"""Minimal diagnostic: types and exact values inside the preamble namespace."""
import io, json, os, sys
from contextlib import redirect_stdout
from pathlib import Path

LEAD = Path(__file__).resolve().parents[1] / 'lead'
os.chdir(LEAD)
sys.path.insert(0, str(LEAD))
sys.argv = ['certify_q0_closure.py', '0', '3']
SRC = (LEAD / 'certify_q0_closure.py').read_text().splitlines(keepends=True)
ns = {'__name__': 'iso', '__file__': str(LEAD / 'certify_q0_closure.py')}
with redirect_stdout(io.StringIO()):
    exec(compile(''.join(SRC[:67]), 'iso', 'exec'), ns)
z = ns['z']
print('type(z)     =', type(z), 'len =', len(z))
print('type(z[36]) =', type(z[36]))
print('repr z[33]  =', repr(z[33]))
print('repr z[36]  =', repr(z[36]))
print('z[33]+z[36] =', repr(z[33] + z[36]))
print('quad(...)   =', ns['quad'](z[33] + z[36], z[116] + z[119]))
print('scalar_quad =', ns['scalar_quad'](z[33] + z[36], z[116] + z[119]))
print('lin idx: lin+21+2i+1 for i=0 ->', ns['lin'] + 21 + 1, ' lin+21+2j j=1 ->', ns['lin'] + 21 + 2)
txt = ''.join(SRC)
for pat in ['v=R2*iv.sin(2*b)/2', 'quad(v,', 'return c*b+', 'def fun(box,c=c']:
    print(f'count of {pat!r}:', txt.count(pat))
