import json, glob, os, sys
sys.stdout.reconfigure(encoding='utf-8')
d1 = json.load(open('joint_nested_frozen.json'))
d2 = json.load(open('joint_patch_frozen_v2.json'))
for f, d in [('joint_nested_frozen.json', d1), ('joint_patch_frozen_v2.json', d2)]:
    print('==', f)
    print('   scope:', str(d.get('scope'))[:160])
    print('   numeric_total_unrounded:', d.get('numeric_total_unrounded'))
    print('   z nonzero:', sum(1 for v in d['z'] if v != 0), 'of', len(d['z']))
    print('   faces:', len(d.get('faces', [])), 'edges:', len(d.get('edges', [])))
print()
print('=== existing joint_patch_tight_bound_* records (tight certifier output) ===')
for p in sorted(glob.glob('joint_patch_tight_bound_*.json')):
    r = json.load(open(p))
    sha = r.get('coefficient_sha256', '')
    tag = ('NESTED-567196' if sha.startswith('5671967c') else
           'v2-a856f2c1' if sha.startswith('a856f2c1') else sha[:16])
    print(f"  {os.path.basename(p):34s} fi={r['factor_index']:2d} {r['factor']:10s} "
          f"upper={r['upper']:+.9f} evals={r['evaluations']:6d} "
          f"budget={r['budget_ended']} sha={tag}")
print()
print('=== existing joint_patch_bound_* (older certifier output) ===')
for p in sorted(glob.glob('joint_patch_bound_*.json')):
    r = json.load(open(p))
    print('  ', os.path.basename(p), {k: r[k] for k in r if k != 'coefficient_sha256'},
          'sha', str(r.get('coefficient_sha256', '<none>'))[:16])
