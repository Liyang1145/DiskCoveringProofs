"""R16 geometry: read the delta-chart and patch-kernel scope notes (encoding-safe), and print
the key definitions used by interval_hub_saturated / interval_hub_norm_cartesian."""
import json, sys
from pathlib import Path

sys.stdout.reconfigure(encoding='utf-8', errors='replace')

L = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
for n in ['DELTA-OUTER-CHART.md', 'INTERVAL-PATCH-KERNEL-SCOPE.md',
          'JOINT-PATCH-SEPARABLE-FIBERS.md', 'HIGH-BEARING-BOUNDARY-THEOREM.md']:
    p = L / n
    print('=' * 25, n)
    if not p.exists():
        print('ABSENT')
        continue
    try:
        t = p.read_text(encoding='utf-8')
    except UnicodeDecodeError:
        t = p.read_text(encoding='utf-8', errors='replace')
    print(t[:2500])
    print()

print('=' * 25, 'interval_hub_norm_cartesian.py')
p = L / 'interval_hub_norm_cartesian.py'
try:
    print(p.read_text(encoding='utf-8'))
except UnicodeDecodeError:
    print(p.read_text(encoding='utf-8', errors='replace'))
