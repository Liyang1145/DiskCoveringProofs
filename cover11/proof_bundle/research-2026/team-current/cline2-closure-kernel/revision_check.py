"""Fresh-check: which kernel revision produced the frozen bounds, and what the newest debug run says."""
import json
import time
from pathlib import Path

L = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
names = ['certify_q0_closure.py', 'debug_middle_inward.py', 'certify_middle_inward.py',
         'check_middle_sector_symbolic.py', 'middle_inward_frozen.json',
         'middle_sector_symbolic_control.json', 'middle_inward_debug_21.json',
         'middle_inward_bound_21.json']
print('name'.ljust(46), 'size'.rjust(7), '  mtime')
for n in names:
    p = L / n
    if p.exists():
        st = p.stat()
        print(n.ljust(46), str(st.st_size).rjust(7), ' ', time.strftime('%H:%M:%S', time.localtime(st.st_mtime)))

print('\n--- middle_inward_debug_21.json (newest debug run) ---')
print((L / 'middle_inward_debug_21.json').read_text())
print('--- middle_sector_symbolic_control.json ---')
print((L / 'middle_sector_symbolic_control.json').read_text())
print('--- middle_inward_bound_21.json ---')
print((L / 'middle_inward_bound_21.json').read_text())
print('--- middle_inward_debug_22.json ---')
p = L / 'middle_inward_debug_22.json'
print(p.read_text() if p.exists() else 'absent')
