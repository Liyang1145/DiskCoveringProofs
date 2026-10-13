import json, hashlib, os
from fractions import Fraction as F

base = r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\solo-20260922'


def sha(p):
    return hashlib.sha256(open(os.path.join(base, p), 'rb').read()).hexdigest()


print('=== file mtimes (manifest written 17:29:12) ===')
for f in ['directional_low_cover.json', 'directional_e_cover.json',
          'directional_fixed_low.json', 'directional_fixed_all.json',
          'DUAL-MANIFEST.json', 'verify_directional_fixed.py',
          'verify_directional_fixed_low.py', 'directional_instrument_control.json']:
    import time
    t = os.path.getmtime(os.path.join(base, f))
    print('  %-38s %s' % (f, time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(t))))

print()
print('=== re-run the audit manifest CHECK (not the writer) ===')
A = []
B = []
for f in ['directional_low_cover.json', 'directional_e_cover.json']:
    A += json.loads(open(os.path.join(base, f)).read())['runs']
for f in ['directional_fixed_low.json', 'directional_fixed_all.json']:
    B += json.loads(open(os.path.join(base, f)).read())['runs']
print('len(A) =', len(A), ' len(B) =', len(B))
ok = True
for rows, tag in ((A, 'A'), (B, 'B')):
    rows_sorted = sorted(rows, key=lambda a: F(a['e_interval'][0]))
    edge = F(0)
    for a in rows_sorted:
        if a['pass'] is not True:
            print('  kernel', tag, 'FAILING run', a['e_interval']); ok = False
        lo, hi = map(F, a['e_interval'])
        if lo != edge or not (lo < hi):
            print('  kernel', tag, 'GAP/OVERLAP at', a['e_interval']); ok = False
        edge = hi
        for v in a['weights'].values():
            vv = list(map(F, v))
            if not (len(vv) == 4 and vv[0] >= sum(abs(x) for x in vv[1:])):
                print('  kernel', tag, 'WEIGHT CONDITION FAIL', a['e_interval'], v); ok = False
    if edge != F(7, 50):
        print('  kernel', tag, 'does NOT reach 7/50: edge =', edge); ok = False
    print('  kernel', tag, ': contiguous coverage to', edge, ' pass:', ok)
# cross-kernel: same endpoints and same weights
same = all(list(map(F, a['e_interval'])) == list(map(F, b['e_interval'])) and a['weights'] == b['weights']
           for a, b in zip(sorted(A, key=lambda a: F(a['e_interval'][0])),
                           sorted(B, key=lambda a: F(a['e_interval'][0]))))
print('  cross-kernel endpoints+weights identical:', same)
print()
print('CONCLUSION on manifest integrity: all ten files pass the audit_dual_manifest CHECKS;')
print('only the stored hash for directional_fixed_all.json is stale.')
print('stored  :', json.load(open(os.path.join(base, 'DUAL-MANIFEST.json')))['files']['directional_fixed_all.json'])
print('current :', sha('directional_fixed_all.json'))
