from pathlib import Path

p = Path(__file__).with_name('joint_oracle_attack_new4.py')
s = p.read_text(encoding='utf-8')
old = "'sum_y': float(np.sum(w and 1.0)),"
new = "'sum_y': float(np.sum(np.concatenate([res.x[:8], [1 - np.sum(res.x[:8])]]))),"
assert old in s, 'sum_y line not found'
s = s.replace(old, new, 1)
stray = "    dummy = solve(np.asarray(y8, dtype=float), maxiter=1)     # obtains a consistent x0 via unpack\n"
if stray in s:
    s = s.replace(stray, "", 1)
p.write_text(s, encoding='utf-8')
print('patched sum_y + stray solve removed')
