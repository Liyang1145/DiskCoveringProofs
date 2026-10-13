# -*- coding: utf-8 -*-
"""Patch the C862b/C862c notes with the lead's three corrections + the interface result."""
import io
from pathlib import Path
B = Path(__file__).resolve().parent.parent

# ---------------------------------------------------------------- C862c
p = B / 'C862c-PINCHED-STATIONARITY.md'
s = io.open(p, encoding='utf-8').read()
s = s.replace(
    "    <n1, Hess(theta1) n1^perp> * L1 = +1 ,   <n2, Hess(theta2) n2^perp> * L2 = -1 .",
    "    <n1, Hess(theta1) n1^perp> * L1^2 = -1 ,   <n2, Hess(theta2) n2^perp> * L2^2 = -1\n"
    "[CORRECTED per lead: the mixed entry scales as 1/L^2, so multiplying by L^2 gives the\n"
    " constant -1; an earlier version printed \"*L = +-1\", which is dimensionally wrong.]")
s = s.replace(
    "(R4) stationarity:  alpha = sum_j c_j n_j - sum_j a_j grad theta_j   (two scalar equations).",
    "(R4) stationarity [CORRECTED per lead: the quadratic terms must be included]:\n"
    "        alpha + sum_j 2 beta_j L_j n_j  =  sum_j c_j n_j - sum_j a_j grad theta_j ,\n"
    "     where alpha = (r(1-cos T cos D), -r cos T sin D) is the gradient of the AFFINE part\n"
    "     ONLY.  My earlier R4 string omitted the sum_j 2 beta_j L_j n_j term (order 2*0.70*0.4\n"
    "     ~ 0.6 per component), inconsistent with the Hessian 2(beta1+beta2) I had written.\n"
    "     After the fix: analytic gradient vs finite differences of the verified Cartesian\n"
    "     objective agrees to 1.2e-10 (tools/interface_check.py, part B).")
s = s.replace(
    "    No interior local maximum was found.  Note the second case: lambda_min = -0.0022 is within\n"
    "    noise of zero, i.e. stationary configurations approach SEMIDEFINITE Hessians — exactly the case\n"
    "    the lead warned about, so any future exclusion must handle zero eigenvalues and may not rest on\n"
    "    strict negative definiteness.",
    "    No interior local maximum was found.  [CORRECTED per lead: the second case has\n"
    "    (lambda_min, lambda_max) = (-0.0022, +1.4276), which is INDEFINITE because lambda_max > 0,\n"
    "    NOT semidefinite, and it is a saddle.  I withdraw the phrase \"semidefinite\".  The only\n"
    "    correct remark is that lambda_min happens to sit near zero, so an exclusion argument may\n"
    "    not assume lambda_min is bounded away from 0.]")
if "INTERFACE CHECK" not in s:
    s += ("""

================================================================================
5. INTERFACE CHECK (added after the lead's objection)
================================================================================
The lead correctly demanded that the Cartesian form be checked against the code objective rather
than against my own construction.  tools/interface_check.py compares, at 300 random legal-ish
points, my Cartesian hub factor with the (delta,H)-chart hub part used by the code chain:
   worst |F_cartesian - F_chart|                  = 5.355e-04
   worst |F_cartesian - F_chart - (z3-z1) delta|  = 3.666e-16
with z3-z1 = 0.000464943.  The first number is exactly the delta-linear piece of K that the
cancellation identity absorbs into a1 theta1 + a2 theta2 and which my comparison string omitted;
once it is restored the two forms agree to MACHINE ZERO, so the Cartesian form IS the objective and
the interface is sound.  Part B of the same script confirms the corrected gradient.
""")
io.open(p, 'w', encoding='utf-8').write(s)
print('C862c patched:', all(m in s for m in
      ['* L1^2 = -1', 'alpha + sum_j 2 beta_j L_j n_j', 'INDEFINITE because lambda_max', 'INTERFACE CHECK']))

# ---------------------------------------------------------------- C862b
p2 = B / 'C862b-INTERIOR-CRITICAL.md'
t = io.open(p2, encoding='utf-8').read()
if 'CORRECTIONS FROM THE LEAD' not in t:
    t += ("""

================================================================================
4. CORRECTIONS FROM THE LEAD (applied; see C862c-PINCHED-STATIONARITY.md)
================================================================================
 (i)  The stationarity formula in C862c must include the quadratic gradient:
        grad F = alpha + sum_j 2 beta_j L_j n_j - sum_j c_j n_j + sum_j a_j grad theta_j = 0
      (alpha alone is only the affine part).  The DIAGNOSTICS here were computed by finite
      differences of the full objective, so their |grad| values are unaffected; only the written
      formula was wrong.
 (ii) The mixed entry of the polar-angle Hessian scales as 1/L^2 (times L^2 gives -1); a printed
      "*L = +-1" in the companion note was dimensionally wrong.
 (iii) In the companion note the stationary point with (lambda_min, lambda_max) =
      (-0.0022, +1.4276) is INDEFINITE, not semidefinite; the word was wrong and is withdrawn.
 (iv) The two angle terms have OPPOSITE chirality in the lead's coordinates, so the Hessian used
      in this file (same chirality for both) was that of a neighbouring function; the corrected
      re-run is in C862c.  The DIRECTION of both conclusions (an ND point in the width-legal
      domain exists; the interior stationary points found are not maxima) survives, but the
      numerical eigenvalues in this file are superseded.
 (v)  Interface verified: my Cartesian hub factor equals the code chain's (delta,H) hub part plus
      the absorbed (z3-z1) delta term to 3.7e-16 over 300 points.
""")
    io.open(p2, 'w', encoding='utf-8').write(t)
print('C862b patched:', 'CORRECTIONS FROM THE LEAD' in t)
