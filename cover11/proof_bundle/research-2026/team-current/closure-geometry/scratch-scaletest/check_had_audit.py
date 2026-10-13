import io, re

s = io.open(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\closure-geometry\HUB-ADJACENCY-FINAL-AUDIT.md',
            encoding='utf-8').read()
print('bytes', len(s.encode('utf-8')), 'lines', s.count('\n') + 1)
print()
for m in re.finditer(r'^#{1,3} .*', s, re.M):
    print('  ', m.group(0))
print()
for p in ['V_1 \u2295 R', '4R \u2212 1', '1 \u2212 2R = 6/25', 'a + e = 0.24 + 0.14 = 0.38 = R',
          '3R \u2212 1 = 7/50', 'inner-root circle']:
    print('  ', repr(p), '->', s.count(p))
print()
i = s.find('**(3)')
print(s[i:i + 1100])
