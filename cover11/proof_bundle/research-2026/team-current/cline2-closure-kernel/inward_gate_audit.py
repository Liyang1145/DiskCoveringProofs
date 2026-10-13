"""Audit of lead/certify_middle_inward.py: filter, corner formula, full-box-return, storage.

Reconstructs the script's namespace exactly as it does at runtime (its own truncate+replace
recipe on certify_q0_closure.py), then:
 A. prints the z-indices the RING factor (idx 22) actually consumes,
 B. prints the z-indices the CORNER formula (line 22) consumes,
 C. tests whether corner(t) >= ring2_raw(pi,t,t) on the corner slice (necessary for soundness),
 D. exercises the filter predicate on sample boxes (discard rule sanity).
"""
import hashlib, io, json, math, os, sys
from contextlib import redirect_stdout
from pathlib import Path
from mpmath import iv

LEAD = Path(__file__).resolve().parents[1] / 'lead'
HERE = Path(__file__).resolve().parent
os.chdir(LEAD)
P = LEAD
frozen = P / 'middle_inward_frozen.json'
digest = hashlib.sha256(frozen.read_bytes()).hexdigest()

# --- replicate the script's namespace construction verbatim (no writes) -----------------
sys.argv = ['x', '0', '4']
src = (P / 'certify_q0_closure.py').read_text()
assert src.count('# Heap entries') == 1, 'marker not found exactly once'
src = src.split('# Heap entries')[0].replace(
    "f'q0_closure_dual_{start}_{span}.json'", "'middle_inward_frozen.json'")
ns = {'__file__': str(P / 'certify_q0_closure.py')}
with redirect_stdout(io.StringIO()):
    exec(src, ns)

iv.dps = 30
z = ns['z']
R = ns['R']
I = ns['interval']
uf, lf = ns['upperfloat'], ns['lowerfloat']
factors = ns['factors']
tmin = iv.mpf(75) / 76
za = [float(v.a) for v in z]
print('frozen digest =', digest)
print('parsed z[36],z[37],z[98],z[99] =', za[36], za[37], za[98], za[99])
print('len(factors) =', len(factors), ' factor[22] =', factors[22][0])

# --- A: ring factor 22's own captured parameters -----------------------------------------
name, raw, dom = factors[22]
f = raw
print('\n=== A. ring22 (idx 22) closure captured defaults ===')
print('   co_varnames tail:', f.__code__.co_varnames[-9:])
vals = [float(v.a) for v in f.__defaults__]
for nm, v in zip(f.__code__.co_varnames[-9:], vals):
    print(f'   {nm:4s} = {v:+.9f}')

# --- B: the corner formula's coefficients -----------------------------------------------
print('\n=== B. what certify_middle_inward.py line 22 uses ===')
i = 2
src_line22 = [l for l in (P / 'certify_middle_inward.py').read_text().splitlines()
              if 'return (w-iv.sin(w))' in l]
print('   literal:', src_line22[0].strip())
print(f'   z[z[i]]                 = z[{i}] = {za[i]:+.9f}')
print(f'   z[32+2i]+z[33+2i]       = z[{32+2*i}]+z[{33+2*i}] = '
      f'{za[32+2*i]:+.9f} {za[33+2*i]:+.9f}')
print(f'   z[94+2i]+z[95+2i]       = z[{94+2*i}]+z[{95+2*i}] = '
      f'{za[94+2*i]:+.9f} {za[95+2*i]:+.9f}')
print(f'   (z[113]+z[114])/2       = ({za[113]:+.9f} {za[114]:+.9f})/2')
print(f'   z[71]                   = {za[71]:+.9f}')

print('\n   ring22 closure names -> values (as captured):')
caps = dict(zip(f.__code__.co_varnames[-9:], vals))
for nm in ('mu', 'd', 'e', 'C', 'dl', 'el', 'hl', 'hr'):
    print(f'     {nm:3s} = {caps.get(nm, float("nan")):+.9f}')
print('   corner formula coefficient-by-coefficient vs ring22 closure:')
print(f'     -mu*pi : corner -z[2]*pi        = {-za[2]:+.9f}   ring mu = {caps["mu"]:+.9f}  '
      f'{"MATCH" if abs(-za[2] - caps["mu"]) < 1e-12 else "MISMATCH"}')
print(f'     -d t^2 : corner -(z[{32+2*i}]+z[{33+2*i}]) = {-(za[32+2*i]+za[33+2*i]):+.9f}   '
      f'ring d = {caps["d"]:+.9f}  {"MATCH" if abs(-(za[32+2*i]+za[33+2*i]) - caps["d"]) < 1e-12 else "MISMATCH"}')
print(f'     -e t^2 : ring e = {caps["e"]:+.9f}')
print(f'     -dl t  : corner -(z[{94+2*i}]+z[{95+2*i}]) = {-(za[94+2*i]+za[95+2*i]):+.9f}   '
      f'ring dl = {caps["dl"]:+.9f}  {"MATCH" if abs(-(za[94+2*i]+za[95+2*i]) - caps["dl"]) < 1e-12 else "MISMATCH"}')
print(f'     -el t  : ring el = {caps["el"]:+.9f}')
print(f'     C w    : corner z[71]+(z[113]+z[114])/2 = {za[71] + (za[113]+za[114])/2:+.9f}  '
      f'ring C = {caps["C"]:+.9f}  '
      f'{"MATCH" if abs(za[71] + (za[113]+za[114])/2 - caps["C"]) < 1e-12 else "MISMATCH"}')

# --- C: does corner dominate ring22 on the corner slice? ---------------------------------
print('\n=== C. corner(t) vs ring22_raw(pi,t,t) on the corner slice ===')


def corner_val(t):
    t = iv.mpf(t)
    w = 2 * ns['asin'](R * t)
    return ((w - iv.sin(w)) / 2 - z[2] * iv.pi
            - (z[32 + 2 * 2] + z[33 + 2 * 2]) * t * t
            - (z[94 + 2 * 2] + z[95 + 2 * 2]) * t
            + (z[71] + (z[113] + z[114]) / 2) * w)


worst = None
for k in range(0, 26):
    t = 0.375 + (1.0 - 0.375) * k / 25
    c = corner_val(t)
    r2 = raw([iv.mpf(float(iv.pi.b)), iv.mpf(t), iv.mpf(t)])
    if r2 is None:
        print(f'  t={t:.6f}: ring22 None (qmin) ; corner={float(c.a):+.9f}')
        continue
    cl, cu = float(c.a), float(c.b)
    rl, ru = float(r2.a), float(r2.b)
    ok = cu >= ru - 1e-12
    if worst is None or not ok:
        worst = (t, cl, cu, rl, ru, ok)
    print(f'  t={t:.6f}: corner=[{cl:+.9f},{cu:+.9f}]  ring22=[{rl:+.9f},{ru:+.9f}]  '
          f'dominates: {ok}')

# --- D: filter predicate on sample boxes --------------------------------------------------
print('\n=== D. filter predicate samples (line 15-17) ===')


def filtered_val(box):
    a, u, v = box
    q = (u - v) ** 2 + 4 * u * v * iv.sin(a / 2) ** 2
    q = I(max(iv.mpf(0).a, q.a), min(iv.mpf(4).b, q.b))
    h = R * iv.sqrt(q) / 2
    k = iv.sqrt(1 - h * h)
    lhs = u * v * (k * iv.sin(a) - h * iv.cos(a))
    m = I(max((tmin * tmin).a, (u * u).a, (v * v).a),
          max((tmin * tmin).b, (u * u).b, (v * v).b))
    return lhs, m * h, (float(lhs.b) < float((m * h).a))


for (ac, uc, vc, hh) in [(3.1415, 1.0, 1.0, 1e-3), (0.6, 0.98, 0.98, 1e-3),
                         (0.6, 0.5, 0.5, 1e-3), (3.0, 0.99, 0.99, 1e-2)]:
    box = [I(ac - hh, ac + hh), I(uc - hh, uc + hh), I(vc - hh, vc + hh)]
    lhs, rhs, disc = filtered_val(box)
    print(f'  box a={ac} u={uc} v={vc} h={hh}: lhs.b={float(lhs.b):+.9f} '
          f'rhs.a={float(rhs.a):+.9f}  -> {"DISCARD" if disc else "keep"}')
