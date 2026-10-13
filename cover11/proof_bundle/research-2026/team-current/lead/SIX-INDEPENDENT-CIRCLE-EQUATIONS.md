# Two of eight circle-ratio equations are redundant (analytic, not numeric rank)

Premises: positive intrinsic q0k4 Euclidean triangle disk, shared lengths and interior site angle sums2pi. Thus flat development exists and its boundary is closed. Compute turns tau_i from boundary triangle angles and odd-inverted widths w_i; impose0<w_i<pi. Gauss–Bonnet gives sumw_i=2pi. Hence every tau_i=(w_i+w_(i+1))/2 lies in(0,pi).

Let boundary edges e_i=P_(i−1)P_i have intrinsic length ell_i and unit direction v_i in the developed boundary. Adjacent directions turn tau_i atPi. These are exactly the directions of canonical unit-circle polygon edges with gapsw_i, after one overall rotation. Set q_i=2sin(w_i/2)>0. The intrinsic and canonical boundary closures are
 Σell_i v_i=0,   Σq_i v_i=0.

ChooseR=q_0/ell_0 and require ONLY six ratios q_i/ell_i=R fori1..6 (i.e. matching seven consecutive chords0..6). Subtract scaled closures:
 (R ell_7−q_7)v_7+(R ell_8−q_8)v_8=0.
Directionsv7,v8 differ by tau_7 (the turn atP7), strictly between0andpi. They are linearly independent. Therefore Rell7=q7 and Rell8=q8 automatically. Thus the positive full circle system has only SIX independent scale-free equality constraints, not eight; no additional equation fromsumwidths. This is a geometric explanation of the previously numeric rank deficit2.

The reduction is exact on this positive branch; near tau_7=0orpi conditioning can be poor, but strict branch still valid. For interval work either use all8redundant equalities or select an adjacent pair with turn separated from0/pi; cannot discard domain checks. At least one adjacent turn has sin bounded? Not asserted without proof. Global infimum remains covered viaC837; every assignment used must satisfy positivity, w range, shared lengths, and interior angle sums EXACTLY, not merely residual-small.

Reduced intrinsic variables:42triangle/switch angles+20local log radii. Constraints11triangle sums+2hub sums+21side matches+6circle ratios=40. Radius objectiveR=q0/ell0. These40rows may still be dependent at special objects; generic rank40 at saved candidate can be checked numerically but not used as proof. Uniform scaling of local radii is present; impose maxradius=1 for minimizer normalization, no all-radii saturation.

Structural gain: eliminateR, all9width variables, and identify2exact redundant circle constraints without assuming equal endpoints or planar shortcuts. Remaining global obligation is this21dim normalized positive shape optimization, now with exact realization converse and degeneracy-safe infimum reduction.
