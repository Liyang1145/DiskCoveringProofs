from pathlib import Path

p = Path(__file__).with_name('joint_oracle_attack_new4.py')
s = p.read_text(encoding='utf-8')
bad1 = "    y_vertex = [(L_CAP - (m_small if k == j else L_CAP)) / D_CAP for j in range(9)]     # y = e_k"
bad2 = "    y_vertex = [(L_CAP - (m_small if k == j else L_CAP)) / D_CAP for j in range(9)]"
good = "    y_vertex = [np.eye(9)[j] for j in range(9)]      # vertex j: widths (m at j, L elsewhere) => y = e_j"
n = 0
if bad1 in s:
    s = s.replace(bad1, "    " + good.strip(), 1)
    n += 1
if bad2 in s:
    s = s.replace(bad2, good.strip(), 1)
    n += 1
assert n > 0, 'vertex builder not found'
p.write_text(s, encoding='utf-8')
print('fixed vertex builder (%d site(s))' % n)
