# Angular boxes and shared-edge area loss

This addendum proves r_D(26)>2287/10000=0.2287. Use U=228701/1000000
in the strict normalization in PROOF.md. Use the signed owner fan identity,
the ideal owner positions, and the allocation of residuals from
FAN-CORRECTION.md. The previous upper construction gives
r_D(26)<=0.234700091.

Let A=3 sqrt(3)/4. Work with triangle areas divided by U^2. A one-edge
group loses more than e0=0.0387 compared with A+1/2, by the rational
Young bound. A two-edge group loses more than 0.097 compared with A+1,
by the common-disk Heron bound. For b other than 16 or 17, use e0 per edge.
For b=16,17, use e=0.0475 per edge. A two-edge group pays 2e on its own.

For a one-edge group with adjacent owner half-angles t,u, set
d=pi/b, J(t)=G_U(d)+G_U'(d)(t-d)-G_U(t). Let v be the sum of the two
fan slacks s_i x_i. These quantities are nonnegative. The additional
allocated loss is (J(t)+J(u)+v)/(2U^2). If J(t)+J(u)+v is at least
B=2(e-e0)U^2, the group is certified. Otherwise, the two angles lie
within d+-0.023, by convexity of J and the checked endpoint inequalities.

On an angular rectangle, let J0 be a lower bound on J(t)+J(u), let
ell be an upper bound on the ideal site separation divided by U,
and let s0 be a positive lower bound on min(sin(t),sin(u)).
The law of cosines and the monotonicity of the ideal radius a(t)
give ell from endpoint radii and the upper bound on (t+u)/2.
The actual normalized edge length X is at most ell+v/s0^2.
Also 0<=v<=B-J0 in the remaining case. If J0>B there is no such case.

For any positive slope D=f'(z), the concavity of
f(X)=X/2+X sqrt(1-X^2/4) on [0,2] gives
f(X)<=f(z)+D(ell-z)+Dv/s0^2. For example, differentiating twice
gives f''(X)=X(X^2-6)/(8(1-X^2/4)^(3/2)) in the interior.
Thus a lower bound on the total normalized loss is

    A+1/2 - f(z) - D(ell-z) + J0/(2U^2)
        + min(0, 1/(2U^2)-D/s0^2) (B-J0).

The checker tries finitely many rational z with positive D. It bisects
a rectangle if its current bounds do not prove the target loss e.
It starts with the full closed angular square and checks both children
of every split. It processes 129 rectangles for b=16 and 11 for b=17.
No numerical optimizer is used for acceptance.

Summing the groups gives an area upper bound of

    (50-b) A U^2 + (b/2) U^2 + b G_U(pi/b) - b e_b U^2,

where e_b is e or e0 as above. The checker verifies strict inequality
with pi for every b from 14 to 26. The smallest certified gap exceeds
0.00011486. The arithmetic uses outward-rounded BigInt intervals.
The rounded gaps in the output are for display only. Replay with
`node verify_fan_boxes.js`. The proof of the strict lower bound uses
the compactness and enlargement arguments in PROOF.md.

The exact optimum remains unresolved. The next goal is to prove
r_D(26)>0.23 by coupling the local losses around the full cyclic
sequence of owner angles and center positions. In particular, the
sum of the owner half-angles is fixed, whereas this certificate
bounds the local residual for each edge group separately.

