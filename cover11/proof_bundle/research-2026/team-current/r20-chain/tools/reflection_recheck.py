"""Reflection-map re-check (lead's objection): is y'_i = y_{2-i} the correct transport?

Definitions (canonical chart, as in FULL-P-ORACLE-THEOREM.md):
   theta_i = i*L - D*sum_{j<i} y_j,  i=0..8,  theta_0 = 0,  sum y = 1, y>=0.
Check:
  (A) the gap identity  theta_{i+1} - theta_i = L - D*y_i  (so y_i owns the gap [theta_i,theta_{i+1}],
      i.e. the anchor gap i -> i+1 = anchor U_i).
  (B) with p(i)=(4-i)%9 (sites), a(i)=(3-i)%9 (anchors), the reflected coordinates satisfy
      theta'_i = theta_3 - theta_{(3-i)%9} (+2pi when unwrapped past theta_3) and then
      theta'_{i+1} - theta'_i = L - D*y_{(2-i)%9},  i.e.  y'_i = y_{(2-i)%9}.
  (C) my earlier claim  theta'_i = theta_1 + theta_2 - theta_{(3-i)%9} and the claimed
      "palindromic" invariance y = rho(y) -- both to be tested and retracted if false.
"""
import json, math
from pathlib import Path

P = Path(__file__).resolve().parent.parent.parent / "lead"
OUT = Path(__file__).resolve().parent.parent / "out"
log = []
def W(x):
    log.append(str(x)); print(x)

cert = json.loads((P / "canonical_local_patch_certificate.json").read_text())
y = [float(eval(v)) for v in cert["center_y"]]
L = 2 * math.asin(19 / 50); D = 9 * L - 2 * math.pi
th = [i * L - D * sum(y[:i]) for i in range(9)]
W(f"L = {L!r}\nD = {D!r}")
W(f"y (certificate centre_y) = {[round(v,10) for v in y]}")
W(f"   sum y = {sum(y):.15f}")
W(f"theta = iL - D*prefix = {[round(v,10) for v in th]}")

W("\n(A) gap identity theta_{i+1}-theta_i == L - D*y_i :")
gapres = [(th[i + 1] - th[i]) - (L - D * y[i]) for i in range(8)]
W(f"   residuals = {[round(v,4e0 and 16) for v in gapres]}   max|.| = {max(abs(v) for v in gapres):.3e}")

W("\n(B) reflected coordinates via the ANCHOR map a(i)=(3-i)%9 (lead's formula):")
thp = []
for i in range(9):
    v = th[3] - th[(3 - i) % 9]
    while v < 0:      # unwrap into [0,2pi)
        v += 2 * math.pi
    thp.append(v)
W(f"   theta' = theta_3 - theta_(3-i) unwrapped = {[round(v,10) for v in thp]}")
W(f"   theta'_0 = {thp[0]:.3e}  (must be 0 for the chart pin)")
gapp = [thp[i + 1] - thp[i] for i in range(8)]
W(f"   gaps' = {[round(v,10) for v in gapp]}")
W(f"   check gap'_i == L - D*y_{(2-i)%9}:  residuals = "
  f"{[round(gapp[i] - (L - D * y[(2 - i) % 9]), 16) for i in range(8)]}")
W(f"   => y'_i = y_{{(2-i)%9}} supported: "
  f"{all(abs(gapp[i] - (L - D * y[(2 - i) % 9])) < 1e-9 for i in range(8))}")

W("\n(C) my earlier claims:")
# claim C1: y = rho(y)  (palindromic invariance)
ry = [y[(2 - i) % 9] for i in range(9)]
W(f"   y            = {[round(v,6) for v in y]}")
W(f"   rho(y)=y_2-i = {[round(v,6) for v in ry]}")
W(f"   max |y - rho(y)| = {max(abs(y[i]-ry[i]) for i in range(9)):.6f}   "
  f"=> palindromic-invariance claim is {'TRUE' if max(abs(y[i]-ry[i]) for i in range(9))<1e-9 else 'FALSE'}")
W(f"   specific: y_1 = {y[1]:.10f}   y_8 = {y[8]:.10f}   equal? {abs(y[1]-y[8])<1e-12}")
W(f"             y_2 = {y[2]:.10f}   y_7 = {y[7]:.10f}   equal? {abs(y[2]-y[7])<1e-12}")
# claim C2: theta'_i = theta_1+theta_2-theta_{3-i}
res_myformula = []
for i in range(9):
    v = th[1] + th[2] - th[(3 - i) % 9]
    v = (v - thp[i] + math.pi) % (2 * math.pi) - math.pi
    res_myformula.append(v)
W(f"   (theta_1+theta_2-theta_(3-i)) - theta'_i (mod 2pi): "
  f"{[round(v,6) for v in res_myformula]}   max|.| = {max(abs(v) for v in res_myformula):.4f}"
  f"  => my pin formula is {'WRONG' if max(abs(v) for v in res_myformula)>1e-6 else 'right'}")

W("\nSUMMARY")
W("   - anchor reflection a(i)=(3-i)%9 is the valid one (lead):  theta'_i = theta_3 - theta_(3-i)")
W("   - the induced width transport is y'_i = y_{(2-i)%9}: the ORIGINAL source was RIGHT")
W("   - the axis is the line through anchor 3 (theta_3), NOT a half-integer index; the")
W("     'off-by-one' flag in ORACLE-CHART-INDEX-AUDIT.md section 6 was itself off by one")
W("     and must be retracted; the 'y = rho(y) at this root' claim is also FALSE")

(OUT / "reflection_recheck.txt").write_text("\n".join(log) + "\n")
print("wrote", OUT / "reflection_recheck.txt")
