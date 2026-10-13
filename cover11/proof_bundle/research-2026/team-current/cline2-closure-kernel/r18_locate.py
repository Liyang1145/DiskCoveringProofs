"""Locate + read the face-arc calibration artifacts and check the stationary Taylor enclosure."""
import hashlib, json, sys, time
from pathlib import Path

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
L = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
for n in ['check_face_derivative_outer.py', 'face_derivative_outer_control.json',
          'stationary_face_bound_probe.json', 'face_second_jet.py',
          'check_face_second_jet.py', 'check_stationary_taylor.py']:
    p = L / n
    if p.exists():
        b = p.read_bytes()
        h = hashlib.sha256(b).hexdigest()[:12]
        ts = time.strftime('%H:%M', time.localtime(p.stat().st_mtime))
        print(f'{n:38s} {len(b):7d} sha={h} {ts}')
    else:
        print(f'{n:38s} ABSENT')

print()
for n in ['check_face_derivative_outer.py']:
    p = L / n
    if p.exists():
        print('=' * 20, n)
        print(p.read_text(encoding='utf-8', errors='replace'))
