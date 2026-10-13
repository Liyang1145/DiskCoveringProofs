# Unrestricted elementary lower bound r_D(12)>1/3

Scope: every twelve-disk covering of the unit closed disk, arbitrary centers in R², all degeneracies allowed. Analytic proof, independent of the saved candidate or n11 classification.

Suppose r<1/3. Every boundary-active disk covers an arc of halfwidth≤asin r. Since sin(π/9)>1/3, nine disks cannot cover the unit circle; hence k≥10 boundary-active disks, leaving at most two others.

The trigonometric strict inequality can be established without a decimal π: let s=sin(π/9)∈(0,1/2). The function g(x)=3x-4x³ is strictly increasing on [0,1/2]. If s≤1/3 then sqrt(3)/2=sin(π/3)=g(s)≤g(1/3)=23/27, contrary to 3/4>529/729 (2187>2116). Thus s>1/3.

Put a=1-2r>r. No boundary-active disk meets the open core B(0,a): its center norm is at least1-r and the reverse triangle inequality gives distance>r. Therefore by finite-union closedness, the remaining at most two disks cover the closed core B(0,a), in particular its boundary circle.

But a disk of radius r<a covers on S(0,a) an arc of halfwidth at most asin(r/a)<π/2 (the same radial AM-GM bound after scaling by a). Two such disks cover total angular measure less than2π, a contradiction. Empty intersections, tangencies, duplicates and a disk centered0 do not escape the argument. Thus r≥1/3.

## Excluding the endpoint

At r=1/3 the same boundary count gives at least10 active disks. Every such center has norm≥2/3, so its intersection with S(0,1/3) is either empty or a singleton (equality in the triangle inequality). At most two hubs cover the core. If neither is0, each covers strictly less than a semicircle of S(0,1/3): for a nonzero center of norm t the condition is cosθ≥t/(2r)>0, or the arc is empty. Hence at least one hub is exactly0. If the other hub is also0 or absent, their common core boundary is all S(0,r); otherwise that other hub leaves an open arc of S(0,r) uncovered.

Choose a point x on this open arc avoiding the finitely many tangency points of the active disks. (In the both-zero/absent case choose any point avoiding those tangencies.) Then every disk except those centered0 is strictly farther than r from x. Continuity preserves those strict inequalities at x_ε=(1+ε)x for all sufficiently small ε>0, whereas disks centered0 also fail there because ||x_ε||>r. Choose ε with ||x_ε||<1. This contradicts full coverage.

No covering exists for r≤1/3. Compact attainment C925 then yields r_D(12)>1/3, not merely a possibly unattained infimum1/3. This is still nonsharp and does not identify the optimum; the main search domain is now (1/3,U].
