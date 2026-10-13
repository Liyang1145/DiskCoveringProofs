from pathlib import Path

p = Path(__file__).with_name('joint_oracle_attack_new4.py')
s = p.read_text(encoding='utf-8')
bad = "\ny_vertex = [np.eye(9)[j] for j in range(9)]      # vertex j: widths (m at j, L elsewhere) => y = e_j"
good = "\n    y_vertex = [np.eye(9)[j] for j in range(9)]   # vertex j => y = e_j"
assert bad in s, 'module-level y_vertex line not found'
s = s.replace(bad, good, 1)
p.write_text(s, encoding='utf-8')
print('indentation fixed')
