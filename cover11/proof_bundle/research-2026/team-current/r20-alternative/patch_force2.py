from pathlib import Path

p = Path(__file__).with_name('fixed_oracle_force_proposal.py')
s = p.read_text(encoding='utf-8')
old = "'min_edge_residual': sol['min_edge_residual'],"
new = "'min_edge_residual_all69': sol['min_edge_residual_all69'],"
assert old in s, 'print key line not found'
s = s.replace(old, new, 1)
p.write_text(s, encoding='utf-8')
print('fixed print key')
