"""R17 locate + hash-pin the ridge artifacts."""
import hashlib, re, sys, time
from pathlib import Path

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
L = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
for n in ['RIDGE-RANK-ONE-COUPLING.md', 'ridge_tangent_jet.py', 'check_ridge_split.py',
          'ridge_split_control.json', 'certify_ridge_tangent.py', 'patch_ridge_jet.py',
          'ridge_tangent_certificate.json']:
    p = L / n
    if p.exists():
        b = p.read_bytes()
        h = hashlib.sha256(b).hexdigest()[:16]
        ts = time.strftime('%m-%d %H:%M', time.localtime(p.stat().st_mtime))
        print(f'{n:34s} {len(b):7d} sha256={h} {ts}')
    else:
        print(f'{n:34s} ABSENT')

print('\nall ridge-named files:')
for p in sorted(L.iterdir()):
    if p.is_file() and re.search(r'ridge', p.name, re.I):
        print(f'   {p.name:44s} {p.stat().st_size:8d}')
