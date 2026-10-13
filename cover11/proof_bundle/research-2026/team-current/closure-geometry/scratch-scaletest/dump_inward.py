import io, os

base = r'C:\Users\袁力阳\Desktop\ai4math2\research-2026'
files = [
    (r'solo-20260922\INNER-ROOT-DOMINANCE.md', 'C464 inner root'),
    (r'solo-20260922\N11-LOW-RADIUS-REDUCTION.md', 'C450/C451 reduction'),
    (r'solo-20260922\M10-038-EXCLUSION.md', 'C450 m=10 theorem'),
]
out = r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\closure-geometry\scratch-scaletest\inward_sources.txt'
with io.open(out, 'w', encoding='utf-8') as f:
    for rel, tag in files:
        p = os.path.join(base, rel)
        s = io.open(p, encoding='utf-8').read()
        f.write('\n\n########## %s : %s (%d bytes) ##########\n' % (tag, rel, len(s.encode('utf-8'))))
        f.write(s)
print('written', out)
