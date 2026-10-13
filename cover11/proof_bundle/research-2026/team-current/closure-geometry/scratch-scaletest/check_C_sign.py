import json

files = [
    ('q0(4,9)  q0_moment_dual_0_2.json', 'q0_moment_dual_0_2.json'),
    ('q1 A      shared_moment_dense_0_4.json', 'shared_moment_dense_0_4.json'),
    ('q1 B      shared_moment_dense_2_4.json', 'shared_moment_dense_2_4.json'),
    ('k3(5,8)   q0_closure_dual_0_3.json', 'q0_closure_dual_0_3.json'),
    ('k4(6,7)   q0_lower375_dual_0_4.json', 'q0_lower375_dual_0_4.json'),
]
for label, f in files:
    row = json.load(open(f))
    z = row['z']
    print(label)
    print('   len(z) = %d' % len(z))
    print('   z[71] = %+.12f      z[72] = %+.12f' % (z[71], z[72]))
    # what slot does C use?
    print('   C(ring) in that kernel = z[lam]=z[71] + (z[72] if i>=3)  ->  >= 0?  min over i: %.12f'
          % min(z[71], z[71] + z[72]))
    print('   z[50:71] (pi-block, nonneg) min = %+.12f' % min(z[50:71]))
    print('   z[73:] min = %+.12f' % (min(z[73:]) if len(z) > 73 else float('nan')))
    print()
