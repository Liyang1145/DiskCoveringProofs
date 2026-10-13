# Exact separability: seven-factor supremum becomes four outer variables and three scalar fibers

Scope: conditional flat sector2, actual inward q0 patch; necessary relaxation keeps local arc coverage, two site-face circumradii<=r, and hubnorm<=1-r; omits external nearest inequalities. Use boundary-first coordinates (r,b1,b2,A,w1,w3,H), B=b1+b2-A. See FLAT-PATCH-ARC-CHART.md and C848.

At fixed (r,b1,b2,A), admissible widths lie independently in [g,W(r,b1)] and [g,W(r,b2)] (empty if W<g); H independently lies in C848 interval. The three intervals are independent because c1,c2,c3,hub are already determined by r,b1,b2,A,H, whereas w1,w3 only select the preceding/following boundary switches. No external nearest constraints have been imposed here. The inwardnorm assures the sector angle branch: w<=W<=2asinr, and |c1|<=s<=cos(w/2), so c1 is on the inward side of chordP0P1; the oriented angle alpha belongs(0,pi], includingpi at chordmidpoint. This supplies the missing branch justification without assuming strictpositiveheight.

For the frozen proposal joint_patch_frozen_v2.json, all z50..z72=0. The seven-factor sum separates EXACTLY as
 F=K(r,b1,b2,A)+F_H(H;r,b1,b2,A)+F_1(w1;r,b1)+F_3(w3;r,b2).
Indeed the two site triangles contain H but no outer widths, the two switch triangles contain neither, and each outer sector depends only on its own width and its fixed center. The middle sector depends only onr. All dual terms are sums of these same atom contributions. Shared matching cancellations do not introduce products between H andwidths. Therefore
 sup_{w1,w3,H} F = K + sup F_H + sup F_1 + sup F_3
on every nonempty fiber. This is an exact supremum identity, not Jensen, not an exchange of max andmin, not independence of the originalsevenfactors. Outer optimization remains in FOUR variables (r,b1,b2,A), with three univariate inner optimizations. May further enlarge r upperboundU toR0 safely.

## Concrete reduced expression and independent calibration
`check_joint_reduced.py` gives the full edge-length/area expression, independently summed against originalsevenatoms on8964 generatedpatches, maxdifference2.24e-13. The analyticreason is trianglearea=DHsinA/2 and sine-law radii-times-sines = physicaledge/(2R0); exactmatching cancellation. Those checks calibrate the implementation, not prove a supremumbound.

## Explicit outer-width component (left; right reflected)
Put c=c1 fixed, P=P0(w), d²=|P-c|², u=sqrt(d²)/R0, and alpha=angle(P-c,P1-c). Let L be the sector baseangle atP. With mu=z1,h=z112,dcoef=z34,lcoef=z96,
 F1(w)=r R0 u sin(alpha)/2 +(w-sinw)/2 -mu alpha-dcoef u²-lcoef u+h(L+w/2),
up to constants independent ofw. The corresponding right function substitutes z3,z115,z39,z101, and uses reflectedbaseangle. The exact derivative is
 F1'(w)=(1-c·P)[1/2+(-mu-h)/|P-c|²]+h+(2dcoef+lcoef/u) cross(c,P)/R0².
Derivation: alpha'=(1-c·P)/d²; (u²)'=-2cross(c,P)/R0²; (L+w/2)'=1-alpha'; total sectorarea'=(1-c·P)/2. The derivative has NO fixedpositive sign for thecurrentfrozencoefficients: numericcounterexample in width_derivative_probe.json, so endpoint-only maximization is NOT justified. Exactunivariateintervalbounds remain possible.

No joint continuum uppercertificate yet. This separability removes the need for naive seven-dimensional box branching without restricting asymmetry or assuming saturation.
