"""Does (D1) [s_j in (r-a,r+a), s1 s2 <= r^2-a^2] plus (D3) [delta >= 2pi-b1-b2]
characterise core covering exactly?  And is (D1) alone sufficient? (expected: no)"""
import numpy as np
r = 0.38; a = 1-2*r
def beta(s): return np.arccos((a*a+s*s-r*r)/(2*a*s))
def covered(s1, s2, d, n=200000):
    h1 = np.array([s1, 0.0]); h2 = s2*np.array([np.cos(d), np.sin(d)])
    t = np.linspace(0, 2*np.pi, n, endpoint=False)
    P = a*np.stack([np.cos(t), np.sin(t)], 1)
    return bool(np.all(np.minimum(np.linalg.norm(P-h1, axis=1), np.linalg.norm(P-h2, axis=1)) <= r))

tests = [
    ("D1 equality, delta=0  (D1 holds, D3 fails)", np.sqrt(r*r-a*a), np.sqrt(r*r-a*a), 0.0),
    ("D1 equality, delta=pi (D1 holds, D3 holds)", np.sqrt(r*r-a*a), np.sqrt(r*r-a*a), np.pi),
    ("D1 equality, delta=2.0",                     np.sqrt(r*r-a*a), np.sqrt(r*r-a*a), 2.0),
    ("s=(0.20,0.30), delta=pi",                    0.20, 0.30, np.pi),
    ("s=(0.20,0.30), delta=0.5",                   0.20, 0.30, 0.5),
    ("s=(0.29,0.29), delta=3.0",                   0.29, 0.29, 3.0),
    ("s=(0.145,0.60), delta=pi",                   0.145, 0.60, np.pi),
]
print("r=%.2f a=%.2f  r-a=%.3f  sqrt(r^2-a^2)=%.6f" % (r, a, r-a, np.sqrt(r*r-a*a)))
print("%-46s D1  D3   direct-coverage" % "case")
for name, s1, s2, d in tests:
    D1 = (r-a <= s1 <= r+a) and (r-a <= s2 <= r+a) and (s1*s2 <= r*r-a*a+1e-15)
    D3 = d >= 2*np.pi - beta(s1) - beta(s2) - 1e-12
    print("%-46s %-3s %-4s %s" % (name, D1, D3, covered(s1, s2, d)))
print("\n(need: direct-coverage == (D3 holds); D1 alone is not sufficient -> first line)")
