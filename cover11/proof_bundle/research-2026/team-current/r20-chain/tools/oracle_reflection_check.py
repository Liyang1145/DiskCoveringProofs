"""ORACLE-CHART-INDEX-AUDIT, part 3: reflection maps and the raw8 chart on the exact root.

Facts checked:
  (a) the canonical angles can[i] = iL - D*sum_{j<i} y_j reproduce canonical_root_angles
      of canonical_local_patch_certificate.json;
  (b) can[i] == raw[(i+2)%9] - raw[2]  (mod 2pi), with can[0]=0 and the 2pi lift at i>=7;
  (c) the canonical reflection y_i' = y_{(2-i)%9} gives theta_i' = theta_2 - theta_{(2-i)%9}
      (mod 2pi), an involution of P fixing the chart index 2;
  (d) the pilot's reflected branch builds its 8 blocks from the vertex set (2-j)%9.
"""
import json, math
from pathlib import Path

P = Path(__file__).resolve().parent.parent.parent / "lead"
OUT = Path(__file__).resolve().parent.parent / "out"
log = []
def W(x):
    log.append(str(x)); print(x)

cert = json.loads((P / "repaired_tc_krawczyk.json").read_text())["certificate"]
z = [float.fromhex(x) for x in cert["center_hex"]][:7]
a = [z[0], z[1], z[2], z[3], math.pi - 2 * sum(z[:4]), z[3], z[2], z[1], z[0]]
th = [0.0] * 9
for k in range(5, 9): th[k] = th[k - 1] + a[k - 1] + a[k]
for k in range(3, -1, -1): th[k] = th[k + 1] - a[k] - a[k + 1]
raw = [th[k] + a[k] for k in range(9)]
L = 2 * math.asin(19 / 50); D = 9 * L - 2 * math.pi
W(f"L = {L:.12f}   D = 9L-2pi = {D:.12f}")
W(f"raw tie azimuths            = {[round(x,7) for x in raw]}")

# reproduces the pilot: lift every raw angle to be >= raw[2], keep raw[2] as the pin
pin = raw[2]
rawm = [(x - pin) % (2 * math.pi) for x in raw]
W(f"(raw - pin) mod 2pi         = {[round(x,7) for x in rawm]}")
can = [rawm[(i + 2) % 9] if i > 0 else 0.0 for i in range(9)]
W(f"can[i] = rawm[(i+2)%9]     = {[round(x,7) for x in can]}")

ref = json.loads((P / "canonical_local_patch_certificate.json").read_text())["canonical_root_angles"]
refmid = [(float(x[0]) + float(x[1])) / 2 for x in ref]
W("compare with canonical_root_angles of the certificate (midpoints):")
W(f"  certificate = {[round(x,7) for x in refmid]}")
W(f"  max |can - certificate| = {max(abs(can[i]-refmid[i]) for i in range(9)):.3e}")

# canonical widths from the certificate's own y-centres
ycen = [float(eval(x)) for x in json.loads((P / "canonical_local_patch_certificate.json").read_text())["center_y"]]
W(f"\ncertificate y-centres = {[round(x,7) for x in ycen]}  sum = {sum(ycen):.10f}")
can2 = [i * L - D * sum(ycen[:i]) for i in range(9)]
W(f"iL - D*prefix(y)       = {[round(x,7) for x in can2]}")
W(f"  max |can2 - can| = {max(abs(can2[i]-can[i]) for i in range(9)):.3e}")

W("\nINDEX CORRESPONDENCE  canonical(i) <-> raw((i+2)%9):")
for i in range(9):
    W(f"   canonical {i}  <-  raw index {(i+2)%9}  (raw azimuth {round(rawm[(i+2)%9],7)})"
      f"  {'[2pi lift applied in the pilot]' if i >= 7 else ''}")

W("\nREFLECTION TRANSPORT:")
yr = [ycen[(2 - i) % 9] for i in range(9)]
canr = [i * L - D * sum(yr[:i]) for i in range(9)]
W(f"  y' = y_(2-i): {[round(x,7) for x in yr]}")
W(f"  theta' = {[round(x,7) for x in canr]}")
res = [math.atan2(math.sin(canr[i] - can[2] + can[(2 - i) % 9]),
                  math.cos(canr[i] - can[2] + can[(2 - i) % 9])) for i in range(9)]
W(f"  theta'_i - theta_2 + theta_(2-i)  (mod 2pi, want 0): "
  f"{[round(x,12) for x in res]}")
W(f"  fixed chart index: 2   (theta'_2 = {round(canr[2],10)}, theta_2 = {round(can[2],10)})")
W("  pilot reflected branch blocks (vertices (2-j)%9):")
for k in range(8):
    i = (k - 2) % 9
    blk = sorted({(2 - j) % 9 for j in range(min(i, 6), max(i, 6))})
    W(f"     k={k}: i=(k-2)%9={i:>2d}  vertex block={blk}")

(OUT / "oracle_reflection_check.txt").write_text("\n".join(log) + "\n")
print("wrote", OUT / "oracle_reflection_check.txt")
