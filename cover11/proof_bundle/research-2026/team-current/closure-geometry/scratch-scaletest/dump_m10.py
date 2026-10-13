import io

p = r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\solo-20260922\M10-038-EXCLUSION.md'
s = io.open(p, encoding='utf-8').read()
out = r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\closure-geometry\scratch-scaletest\m10_full.txt'
with io.open(out, 'w', encoding='utf-8') as f:
    f.write(s)
print('bytes', len(s.encode('utf-8')))
# section headers
for line in s.split('\n'):
    if line.startswith('#'):
        print(line)
