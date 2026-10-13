import io, re

p = r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\closure-geometry\HUB-ADJACENCY-FINAL-AUDIT.md'
s = io.open(p, encoding='utf-8').read()
print('bytes', len(s.encode('utf-8')), 'lines', s.count('\n') + 1)
print()
print('=== residual wrong wording (should be 0) ===')
for pat in ['U \\ ({p} \u2229 U)', 'meets the line `xp` in at most', 'A segment cannot equal',
            'at most a chord of zero area']:
    print('  ', pat.encode('unicode_escape').decode(), '->', s.count(pat))
print()
print('=== corrected wording present ===')
for pat in ['(U \u2229 V_1) \\ {p}', '(U \u2229 V_2) \\ {p}', 'relatively closed in `U \\ {p}`',
            'if the segment `[x,y]` does not contain `p`', 'avoiding both lines `xp` and `yp`']:
    print('  ', pat.encode('unicode_escape').decode(), '->', s.count(pat))
print()
i = s.find('**(2) A point contact')
print(s[i:i + 1500])
