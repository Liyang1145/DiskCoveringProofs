from mpmath import mp
import json

mp.dps = 25
for f in ['shared_moment_dense_0_4.json', 'shared_moment_dense_2_4.json', 'q0_moment_dual_0_2.json']:
    row = json.load(open(f))
    z = row['z']
    print('%-38s  z[71]=%s  z[72]=%s' % (f, z[71], z[72]))
    print('     all z[50:73] nonzero entries:',
          [(i, round(v, 9)) for i, v in enumerate(z) if i >= 50 and abs(v) > 1e-12][:12])
    # also check the linear-multiplier block (73..112) and side/radius block
    print('     z[0:11]:', [round(v, 6) for v in z[0:11]])
    print()
