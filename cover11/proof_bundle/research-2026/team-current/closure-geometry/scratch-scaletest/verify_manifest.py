import json, hashlib, os

base = r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\solo-20260922'

def h(p):
    return hashlib.sha256(open(os.path.join(base, p), 'rb').read()).hexdigest()

man = json.load(open(os.path.join(base, 'DUAL-MANIFEST.json')))
print('=== manifest hash verification ===')
print('declared scope:', man['exact_scope'])
print('intervals:', man['intervals'], ' kernelA boxes', man['kernel_A_boxes'],
      ' kernelB boxes', man['kernel_B_boxes'])
print('weights_and_endpoints_equal:', man['weights_and_endpoints_equal'])
ok = True
for f, hv in man['files'].items():
    got = h(f)
    good = (got == hv)
    ok &= good
    print('  %-38s %s' % (f, 'OK' if good else 'MISMATCH'))
print('all hashes match:', ok)

print()
print('=== e-coverage: two files ===')
for f in ['directional_low_cover.json', 'directional_e_cover.json']:
    d = json.load(open(os.path.join(base, f)))
    runs = d.get('runs', [])
    print('%-30s level=%s start=%s target_end=%s certified_contiguous_end=%s all_covered=%s runs=%d pending=%s'
          % (f, d.get('level'), d.get('start'), d.get('target_end'),
             d.get('certified_contiguous_end'), d.get('all_covered'),
             len(runs), d.get('pending')))
    if runs:
        print('    first run:', json.dumps(runs[0])[:260])
        print('    last  run:', json.dumps(runs[-1])[:260])
