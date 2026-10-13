import io, re

p = r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\flash-structure\GLOBAL-TOPOLOGICAL-REDUCTION.md'
s = io.open(p, encoding='utf-8').read()
out = r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\closure-geometry\scratch-scaletest\gtop_2b.txt'
i = s.find('§2b')
if i < 0:
    i = s.find('q <= 2')
with io.open(out, 'w', encoding='utf-8') as f:
    f.write(s[max(0, i-3000):i+5000])
print('written, offset', i)
