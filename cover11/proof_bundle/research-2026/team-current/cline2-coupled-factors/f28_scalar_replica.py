"""cline2-coupled-factors f28: replicate the lead's scalar dual assembly exactly.

From lead/check_q0_closure_scalar.py the scalar identity is

    D(z, realization) = area + z[50:71].slack + z[71]*(sum ws - 2pi) + z[112:].cls

where the realization is the saved candidate and (A+B)@x0 <= pi is the primal constraint
vector.  On the candidate `area = pi`, so D - pi is exactly the phantom slack the dual
subtracts.  This is the correct way to evaluate the dual at the candidate; my earlier
f9/f16 evaluation mis-normalized (mixed rho/R_cert with R^2) and f26 double-counted, both
of which this script replaces.
"""
import numpy as np, json, math
from pathlib import Path
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
pi = math.pi

src = (LEAD/'q0_exact_closure_radius.py').read_text()
head = src.split('res=ceq(x0)')[0]
ns = {'__file__': str(LEAD/'q0_exact_closure_radius.py'), '__name__': 'q0mod'}
exec(head, ns)
faces = ns['faces']; edges = ns['edges']; x0 = np.array(ns['x0'])
print('faces', len(faces), 'edges', len(edges), 'x0 size', x0.shape)
J = json.loads((LEAD/'q0_closure_dual_0_4.json').read_text())
z = np.array([float(f'{v:.9f}') for v in J['z']])
rrr = 0.38
aa = x0[:33].reshape(11, 3)
bs = x0[33:42]
ys = np.exp(x0[42:62]+x0[-1])/rrr
als, ws, cls, area = ns['calc'](x0)
print(f'area = {area:.15f}  pi = {pi:.15f}  area - pi = {area-pi:+.3e}')
print(f'max normalized radius = {max(ys):.12f}')
print(f'sum ws - 2pi = {sum(ws)-2*pi:+.6e}')
print(f'slack (A+B)@x0, pi - that = {pi-float((ns["A"]+ns["B"])@x0):+.6e}')

const = pi*(sum(z[:9])+2*sum(z[9:11])+sum(z[50:71])-2*z[71])-pi*sum(z[112:])
D = const
for t, f in enumerate(faces):
    D += 2*rrr**2*ys[t]**2*np.prod(np.sin(aa[t]))
    for k, i in enumerate(f):
        e = tuple(sorted(j for j in f if j != i)); ei = edges.index(e)
        adj = [tt for tt, ff in enumerate(faces) if set(e) <= set(ff)]
        sg = 1 if adj[0] == t else -1
        D += (-(z[i]+z[50+ei])*aa[t, k] + sg*z[11+ei]*ys[t]**2*math.sin(aa[t, k])**2
              + sg*z[73+ei]*ys[t]*math.sin(aa[t, k]))
for i in range(9):
    j = (i+1) % 9
    ei = edges.index(tuple(sorted((i, j))))
    b = bs[i]; y = ys[11+i]
    D += (rrr**2*y*y*math.sin(2*b)/2 + (z[i]+z[j]-z[50+ei]+2*z[112+i])*b
          - z[11+ei]*y*y*math.sin(b)**2 - z[73+ei]*y*math.sin(b)
          + (z[32+2*i+1]+z[32+2*j])*y*y + (z[94+2*i+1]+z[94+2*j])*y)
    a = als[i]; u = ys[11+(i-1) % 9]; v = ys[11+i]; w = ws[i]
    L = math.atan2(v*math.sin(a), u-v*math.cos(a)); T = pi-a-L
    D += (rrr**2*u*v*math.sin(a)/2+(w-math.sin(w))/2+z[71]*w-z[i]*a
          - z[32+2*i]*u*u-z[32+2*i+1]*v*v-z[94+2*i]*u-z[94+2*i+1]*v
          + z[112+(i-1) % 9]*L+z[112+i]*T+(z[112+(i-1) % 9]+z[112+i])*w/2)
slack = pi-(ns['A']+ns['B'])@x0
expected = area+z[50:71]@slack+z[71]*(sum(ws)-2*pi)+z[112:]@cls
print(f'\nD = {D:.15f}')
print(f'expected = {expected:.15f}')
print(f'identity error = {abs(D-expected):.3e}')
print(f'D - pi = {D-pi:+.6e}    (this is the phantom slack the dual subtracts)')
print(f'z[71] = {z[71]:.9f}   sum(ws)-2pi = {sum(ws)-2*pi:+.6e}   '
      f'z[112:]@cls = {z[112:]@cls:+.6e}')
print(f'z[50:71]@slack = {z[50:71]@slack:+.6e}')
print(f'\nbound  D + sum_f max_f = {D:.9f} + (factor maxima) ; lead reports '
      f'{J["sample_upper"]:.9f}')
