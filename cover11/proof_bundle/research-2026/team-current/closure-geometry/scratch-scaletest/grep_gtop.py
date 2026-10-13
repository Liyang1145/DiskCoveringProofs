import io, re

s = io.open(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\flash-structure\GLOBAL-TOPOLOGICAL-REDUCTION.md',
            encoding='utf-8').read()
print('bytes', len(s.encode('utf-8')))
out = []
for m in re.finditer(r'.{0,160}(k_1|k_2|13 ?[-−] ?q|degree|degrees).{0,240}', s, re.S):
    t = m.group(0).replace('\n', ' ')
    out.append(t)
with io.open(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\closure-geometry\scratch-scaletest\gtop_grep.txt',
             'w', encoding='utf-8') as f:
    for t in out[:25]:
        f.write('---\n' + t + '\n')
print('wrote', len(out[:25]), 'matches')
