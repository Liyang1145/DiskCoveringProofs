"""Locate the network-envelope artifacts and the STATUS/DEAD files."""
import sys, time
from pathlib import Path

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
L = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
for n in ['interval_network_envelope.py', 'NETWORK-ENVELOPE-QUANTITATIVE-LEMMA.md',
          'FIXED-SWITCH-SHARPNESS-AND-LOCALITY.md']:
    p = L / n
    if p.exists():
        ts = time.strftime('%m-%d %H:%M', time.localtime(p.stat().st_mtime))
        print(f'EXISTS {n:54s} {p.stat().st_size:8d} {ts}')
    else:
        print(f'ABSENT {n}')

print('\nSTATUS / DEAD files under team-current:')
base = L.parent
for d in sorted(base.iterdir()):
    if d.is_dir():
        for f in ('STATUS.md', 'DEAD.md'):
            pp = d / f
            if pp.exists():
                print(f'  {d.name}/{f}  {pp.stat().st_size}')
print('\nlead dir STATUS/DEAD?', (L / 'STATUS.md').exists(), (L / 'DEAD.md').exists())
