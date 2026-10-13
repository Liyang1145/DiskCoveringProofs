"""Fix the remaining wrong identity in the body (G K = 0 -> GᵀK = 0)."""
import sys
from pathlib import Path

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
p = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\closure-kernel'
         r'\NETWORK-ENVELOPE-AUDIT.md')
t = p.read_text(encoding='utf-8')
old = 'script asserts (`B N = 0`, `G K = 0`, `L_ff Y = L_fa`, `G8ᵀG8 · GramInv = I`) is *proved* by'
new = 'script asserts (`B N = 0`, `GᵀK = 0`, `L_ff Y = L_fa`, `G8ᵀG8 · GramInv = I`) is *proved* by'
if old in t:
    t = t.replace(old, new)
    p.write_text(t, encoding='utf-8')
    print('fixed')
else:
    print('PATTERN NOT FOUND; lines containing the assertion list:')
    for i, l in enumerate(t.splitlines(), 1):
        if 'L_ff Y = L_fa' in l:
            print(i, '|', repr(l))
