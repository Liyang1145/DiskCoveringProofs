"""R16 audit: locate and hash-pin the C863 artifacts."""
import hashlib, json, os, time
from pathlib import Path

L = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
names = ['HIGH-BEARING-NORM-EXCLUSION.md',
         'interval_hub_norm_only.py', 'interval_hub_saturated.py', 'interval_hub_boundary.py',
         'certify_patch_norm_boundary.py', 'certify_norm_cartesian_control.py',
         'assemble_norm_boundary.py',
         'patch_outer_norm_boundary_certificate.json', 'norm_cartesian_control_certificate.json',
         '22_manifest.json', 'middle_inward_frozen.json']
print('=== named artifacts ===')
for n in names:
    p = L / n
    if p.exists():
        b = p.read_bytes()
        print(f'{n:46s} {len(b):8d}  sha256={hashlib.sha256(b).hexdigest()[:16]}  '
              f'{time.strftime("%m-%d %H:%M", time.localtime(p.stat().st_mtime))}')
    else:
        print(f'{n:46s} ABSENT')

print('\n=== everything matching the C863 keywords ===')
import re
pat = re.compile(r'(norm_boundary|norm_cartesian|norm_only|hub_sat|hub_norm|22_manifest|cartesian)',
                 re.I)
for p in sorted(L.iterdir()):
    if p.is_file() and pat.search(p.name):
        b = p.read_bytes()
        print(f'  {p.name:52s} {len(b):8d}  '
              f'{time.strftime("%m-%d %H:%M", time.localtime(p.stat().st_mtime))}')
