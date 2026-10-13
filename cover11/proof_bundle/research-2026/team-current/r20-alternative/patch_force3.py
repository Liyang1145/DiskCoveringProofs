from pathlib import Path

p = Path(__file__).with_name('fixed_oracle_force_proposal.py')
s = p.read_text(encoding='utf-8')
old = "    eds = np.array([cc['fun'](res.x) for cc in cons[18:]])"
new = "    eds = np.array([cc['fun'](res.x) for cc in cons])   # ALL 51 edges, in FORCE_ORDER order"
assert old in s, 'eds line not found'
s = s.replace(old, new, 1)
p.write_text(s, encoding='utf-8')
print('fixed edge_residuals to all 51 (order matches FORCE_ORDER)')
