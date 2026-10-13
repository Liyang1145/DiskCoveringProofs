from mpmath import mp, asin, sin, cos, sqrt, pi, mpf
import json

mp.dps = 25
R = mpf(19)/50
print('=== DUAL-MANIFEST.json ===')
m = json.load(open(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\solo-20260922\DUAL-MANIFEST.json'))
print(json.dumps(m, indent=1)[:2000])

print()
print('=== directional_e_cover.json : segments ===')
ev = json.load(open(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\solo-20260922\directional_e_cover.json'))
if isinstance(ev, dict):
    print('keys:', list(ev.keys())[:12])
    segs = ev.get('segments', ev.get('rows', None))
else:
    segs = ev
print('type', type(segs), 'len', len(segs) if segs is not None else None)
if segs:
    print('first seg:', json.dumps(segs[0])[:400])
    print('last  seg:', json.dumps(segs[-1])[:400])
