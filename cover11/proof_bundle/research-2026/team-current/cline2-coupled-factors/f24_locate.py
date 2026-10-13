"""cline2-coupled-factors f24: locate the assembly inconsistency found by the f23 self-test."""
import numpy as np, json, math, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import f23_clean_moments as C

z = np.r_[C.z0lead, np.zeros(C.NZ-121)]
print(f'bound at L=product=0: ', end='')
for label, wf, wp in [('calib', False, False), ('product only', False, True)]:
    F = C.build_factors(wf, wp)
    ub = float(C.B @ z)
    bad = []
    for name, v, M in F:
        val = v+M@z
        j = int(np.argmax(val))
        ub += float(val[j])
        # consistency: does the collected max equal the value at the maximizing sample?
        if abs(float(val[j]) - (float(v[j])+float(M[j]@z))) > 1e-12:
            bad.append(name)
    print(f'\n   {label}: bound={ub:.9f}  inconsistent-so-far={bad}')
    if label == 'product only':
        print('   per-factor value at the max sample:')
        for name, v, M in F:
            val = v+M@z
            j = int(np.argmax(val))
            print(f'      {name:10s} max={val[j]: .9f}  v={v[j]: .9f}  '
                  f'M@z={float(M[j]@z): .9f}')
