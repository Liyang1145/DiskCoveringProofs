"""cline2-coupled-factors R16hh: witnesses for the report (<=200 legal points per face)."""
import math, json, sys, random
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
from r16gg_corrected import corrected, legal

rows = {}
for face in (1, 2):
    cand = []
    for i in range(6):
        r = 0.375+(0.38-0.375)*i/5
        bhi = math.acos(r)
        for a in range(6):
            b1 = 1+(bhi-1)*a/5
            for c in range(6):
                b2 = 1+(bhi-1)*c/5
                for m in range(11):
                    cand.append((r, b1, b2, -b2+(b1+b2)*m/10))
    random.seed(1700+face)
    random.shuffle(cand)
    pts = []
    for (r, b1, b2, dl) in cand:
        if len(pts) >= 200:
            break
        if not legal(r, b1, b2, dl, face):
            continue
        G, G1, G2 = corrected(r, b1, b2, dl, face)
        pts.append((r, b1, b2, dl, G, G1, G2))
    rows[face] = pts
    g1 = [p[5] for p in pts]; g2 = [p[6] for p in pts]
    bl = sorted(pts, key=lambda t: abs(t[5]))[:3]
    print(f'face {face}: {len(pts)} legal pts; G\' range [{min(g1):+.6f},{max(g1):+.6f}];'
          f' G\'\' range [{min(g2):+.6f},{max(g2):+.6f}]')
    print(f"   smallest |G'| legal points (candidate interior extrema):")
    for p in bl:
        print(f"      r={p[0]} b1={p[1]:.6f} b2={p[2]:.6f} d={p[3]:.6f} "
              f"G'={p[5]:+.6f} G''={p[6]:+.6f} G={p[4]:+.6f}")
    sign = [('neg' if p[5] < 0 else 'pos') for p in pts]
    print(f"   G' sign transitions along the sorted-by-G' list: "
          f"{sum(1 for i in range(len(sign)-1) if sign[i] != sign[i+1])}")
    print()
json.dump({str(k): v for k, v in rows.items()}, open(
    Path(__file__).parent/'out'/'r16hh_witness.json', 'w'), indent=1)
print('saved out/r16hh_witness.json')
