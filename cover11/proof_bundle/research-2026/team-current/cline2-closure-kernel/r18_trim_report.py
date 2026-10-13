"""Remove the superseded (old) sections (1) and (4) from the R18 report, keeping the corrected
replacements. Also drop any now-dangling 'witness rule' wording."""
from pathlib import Path

p = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\cline2-closure-kernel\R18-STATIONARY-FACE-AUDIT.md')
lines = p.read_text(encoding='utf-8').splitlines(keepends=True)

# locate headers
idx = [i for i, l in enumerate(lines) if l.startswith('## ')]
new1 = next(i for i in idx if '(1) Stationary Taylor block' in lines[i] and 'CORRECT' in lines[i])
new4 = next(i for i in idx if '(4) Endpoint closure' in lines[i] and 'corrected statement' in lines[i])
old1 = next(i for i in idx if 'sign is inverted' in lines[i])
old4 = next(i for i in idx if 'one class needs naming' in lines[i])
sec2 = next(i for i in idx if lines[i].startswith('## (2)'))

# keep 0..old1-1  (front matter + new (1) + new (4)) then jump to (2)..end
out = lines[:old1] + lines[sec2:]
p.write_text(''.join(out), encoding='utf-8')

t = p.read_text(encoding='utf-8')
for l in t.splitlines():
    if l.startswith('## '):
        print(l)
print('\nold witness-rule block still present?', 'witness rule' in t)
print('old inverted-sign heading present?', 'sign is inverted' in t)
print('old endpoint heading present?', 'one class needs naming' in t)
