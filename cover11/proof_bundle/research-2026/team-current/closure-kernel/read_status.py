"""Read the STATUS/DEAD sections that carry C909 (exact radial stress) and the C891 root."""
import re, sys
from pathlib import Path

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
base = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current')

for rel in ['r20-gluing/STATUS.md', 'r20-stress/STATUS.md', 'r20-chain/DEAD.md']:
    p = base / rel
    if not p.exists():
        continue
    t = p.read_text(encoding='utf-8', errors='replace')
    lines = t.splitlines()
    print('=' * 30, rel, f'({len(lines)} lines)')
    for pat, ctx in [(r'C909', 10), (r'径向', 6), (r'C891', 6)]:
        for i, l in enumerate(lines):
            if re.search(pat, l):
                print(f'  --- match {pat!r} at line {i+1} ---')
                for j in range(max(0, i - ctx), min(len(lines), i + 6)):
                    print(f'   {j+1:4d}| {lines[j][:200]}')
                break
    print()
