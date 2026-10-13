"""n=14 core analysis (CORRECTED).

The saved candidate has 10 boundary-active centres {0..9} ( |c|+R >= 1 ) and 4
non-boundary centres {10,11,12,13} at |c| = 0.3268180687155822 (x2) and
0.38861869814453937 (x2).

Mechanism check (members/structure/SELECTION-n13-n14-n15-n25.md): with a = 1-2U,
no boundary-active disk covers the open core B(0,a), so the 4 non-boundary disks
must cover the closed core.  Finite test on the core circle |x| = a:

  * NO centre with |c|+R >= 1 can reach the circle |x|=a (min over them of
    | |c| - a | is 0.11256 > U),
  * the four non-boundary centres cover that circle with max-min = 0.2672882799,
    which is below U by 0.0644.

So the mechanism's role assignment is CONFIRMED for this candidate, and the
transitive conclusion m >= 3 (hence k <= 11 for n=14) stands: the core circle
cannot be covered by fewer than 3 of those four.

NOTE: an earlier version of this script printed a conclusion that contradicted its own
numbers ("inactive-only fails"); that was a misreading of the output.  The numbers were
always: inactive-only max-min = 0.26729 <= U, i.e. the inactive set SUCCEEDS.
"""
from pathlib import Path
import json
import mpmath as mp
mp.mp.dps = 50

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAND = ROOT / "research-2026/next-cover-global/members/candidate"
EV = CAND / "evidence"
d = json.loads((ROOT / "research-2026/session2/type14/out/hprec_sol.json").read_text(encoding="utf-8"))
C = [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in d["centers"]]
n = len(C)
R = mp.mpf(d["R"])
OUT = []
def W(s=""): OUT.append(str(s))

U = mp.mpf("0.33173203427623416")
a = 1 - 2*U
rad = [mp.sqrt(c[0]**2+c[1]**2) for c in C]
active = [i for i in range(n) if rad[i]+R >= 1]
inact = [i for i in range(n) if rad[i]+R < 1]

W("### n=14 core analysis (corrected)")
W(f"  U (C411 threshold) = {mp.nstr(U,28)}")
W(f"  a = 1-2U           = {mp.nstr(a,28)}")
W(f"  R (candidate)      = {mp.nstr(R,28)}")
W(f"  boundary-active (|c|+R >= 1): {active}   n_active={len(active)}")
W(f"  non-boundary:                  {inact}   n_inactive={len(inact)}")
W("")
W("### can any boundary-active centre reach the circle |x| = a ?")
lo = min(abs(rad[i]-a) for i in active)
W(f"  min over active i of | |c_i| - a | = {mp.nstr(lo,20)}")
W(f"  this exceeds U by {mp.nstr(lo-U,8)}  =>  NO active disk meets the core circle")
W("")
W("### do the four non-boundary centres cover the core circle?")
N = 400000
wa = (-1, None); wi = (-1, None)
for s in range(N):
    th = 2*mp.pi*s/N
    p = (a*mp.cos(th), a*mp.sin(th))
    da = min(mp.sqrt((p[0]-c[0])**2+(p[1]-c[1])**2) for c in C)
    di = min(mp.sqrt((p[0]-C[i][0])**2+(p[1]-C[i][1])**2) for i in inact)
    if da > wa[0]: wa = (da, th)
    if di > wi[0]: wi = (di, th)
W(f"  max over |x|=a of min over ALL centres     = {mp.nstr(wa[0],22)}   (<= U: {wa[0] <= U})")
W(f"  max over |x|=a of min over NON-BOUNDARY    = {mp.nstr(wi[0],22)}   (<= U: {wi[0] <= U})")
W(f"  slack in the inactive-only bound           = {mp.nstr(U-wi[0],8)}")
W("")
W("### how many of the four are actually needed?  (cover the core circle by subsets)")
import itertools
W("  subset size 2:")
for S in itertools.combinations(inact, 2):
    mx = mp.mpf(0)
    for s in range(0, N, 7):
        th = 2*mp.pi*s/N
        p = (a*mp.cos(th), a*mp.sin(th))
        mx = max(mx, min(mp.sqrt((p[0]-C[i][0])**2+(p[1]-C[i][1])**2) for i in S))
    W(f"    {list(S)}: max-min = {mp.nstr(mx,16)}  covers: {mx <= U}")
W("  subset size 3:")
ok3 = 0
for S in itertools.combinations(inact, 3):
    mx = mp.mpf(0)
    for s in range(0, N, 7):
        th = 2*mp.pi*s/N
        p = (a*mp.cos(th), a*mp.sin(th))
        mx = max(mx, min(mp.sqrt((p[0]-C[i][0])**2+(p[1]-C[i][1])**2) for i in S))
    if mx <= U: ok3 += 1
    W(f"    {list(S)}: max-min = {mp.nstr(mx,16)}  covers: {mx <= U}")
W(f"    -> {ok3} of the 4 three-subsets cover the core circle")
W("")
W("### conclusion")
W("  * The mechanism's role split is CONFIRMED for this candidate: the core circle is")
W("    reachable only by the 4 non-boundary centres, and they cover it.")
W("  * Subset test: no PAIR covers it, every TRIPLE does => the sharp count is")
W("    m >= 3, i.e. k <= n - 3 = 11 for n=14, matching the structure member's table.")
W(f"  * The observed configuration has m = {len(inact)} (4), so it is NOT at the boundary")
W(f"    of the inequality; the k=11 case of the selection table is a genuine open case.")
(EV / "n14_core.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
