"""Second trim: remove the remaining old §4 block (lines 140..171, up to §5) and reorder headers
so the corrected (4) sits last, matching 1,2,3,4 numbering."""
from pathlib import Path

p = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\cline2-closure-kernel\R18-STATIONARY-FACE-AUDIT.md')
lines = p.read_text(encoding='utf-8').splitlines(keepends=True)
idx = [i for i, l in enumerate(lines) if l.startswith('## ')]
h = {lines[i].strip(): i for i in idx}
new4 = h['## (4) Endpoint closure — corrected statement']
old4 = h['## (4) Endpoint closure — correct in outline; one class needs naming']
sec5 = h['## (5) Language']

# drop old4..sec5-1
out = lines[:old4] + lines[sec5:]
# now move the corrected (4) block to just before (5)
lines = out
idx = [i for i, l in enumerate(lines) if l.startswith('## ')]
h = {lines[i].strip(): i for i in idx}
new4 = h['## (4) Endpoint closure — corrected statement']
sec2 = h['## (2) `face_derivative_outer_jet.derivative` — formulas verified term by term']
sec5 = h['## (5) Language']
block4 = lines[new4:sec2]
front = lines[:new4]
mid = lines[sec2:sec5]
tail = lines[sec5:]
out = front + mid + block4 + tail
p.write_text(''.join(out), encoding='utf-8')

t = p.read_text(encoding='utf-8')
for l in t.splitlines():
    if l.startswith('## '):
        print(l)
print('\nwitness-rule text present?', 'witness rule' in t)
