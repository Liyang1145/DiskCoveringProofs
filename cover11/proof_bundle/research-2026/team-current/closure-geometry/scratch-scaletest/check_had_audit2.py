import io, re

p = r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\closure-geometry\HUB-ADJACENCY-FINAL-AUDIT.md'
s = io.open(p, encoding='utf-8').read()
print('bytes', len(s.encode('utf-8')), 'lines', s.count('\n') + 1)
print()
print('=== residual wrong text in the body (should be 0) ===')
for pat in ['a := 1 \u2212 2R = 6/25', 'bounded ball', 'hub disk: contains the core',
            'strictly* in the interior when']:
    print('  ', pat.encode('unicode_escape').decode(), '->', s.count(pat))
print()
print('=== corrected content present ===')
for pat in ['a := 1 \u2212 2r', '(1 \u2212 r) \u2212 (1 \u2212 2r)  =  r',
            'non-collinear intermediate point', 'the nine ring disks',
            'Errors of mine that this revision corrects', 'r + 2R \u2212 1']:
    print('  ', pat.encode('unicode_escape').decode(), '->', s.count(pat))
print()
for m in re.finditer(r'^#{1,3} .*', s, re.M):
    print('  ', m.group(0))
