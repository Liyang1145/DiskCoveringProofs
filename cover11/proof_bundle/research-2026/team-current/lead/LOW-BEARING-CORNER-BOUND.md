# Both-low flat-patch corner upper bound

Scope: fixed frozen seven-factor objective, actual r∈[.379,.37999], C849/C850 bearings b1,b2∈[.60946080763725372899,1], legal hub in C858 lens. By C872 both width maxima can be replaced by explicit endpoints. This note bounds ONLY norm-face intersections (both signs, both faces) and the face-face ridge. It does NOT assert maxima occur only at corners.

## Coverage and branches
NORM-FACE-CORNER-CHART.md gives all norm-face intersections. The factored radicand is h²=r²*sin(2b)*(2s(1-r)-s²sin(2b))/(1-2sr sin(2b)). On this domain all factors are strictly positive: sin2b>0; denominator≥(s-r)²>0; 2(1-r)>s because 4(1-r)²-(1-r²)=(1-r)(3-5r)>0. Thus the two intersections are distinct and smooth. Both signs retained.

Two distinct face circles intersect at the origin (excluded by normdisk v>0) and the ridge X=2r sin(b1+b2)(cos(b1-b2),sin(b1-b2)). When b1+b2=pi/2 they coincide: the entire common arc is NOT an intersection corner set and must remain in stationary-arc analysis. Its endpoints are norm-face intersections; no discontinuous sign selection is used.

Opposite-face necessary cap difference on face1 is 4r*cos(b1+b2)*sin(b1-b2-delta)≤0 (reverse sign forface2). The signed filter retains zero and both signs ofcosT; it never imports high-bearing ridge ordering. Direct Cartesian residual also applied.

At a saturated own face let A=b+sigma*delta∈(0,pi). Its source vector is 2r sinA(cosA,sinA); hence e=r sinA/R0 and Cartesian argument phi=A exactly. This removes a redundant square root/pole. It is an analytic extension equal to the physical expression on legal points; derivatives apply to this extension, not a physically clipped expression. At ridge both terms simplify. check_corner_identities.py gives exact symbolic identities; check_low_corners.py compares15 Cartesian intersections and angle-chart values, including both signs and face ridge.

## Bounds
low_corner_jet.py combines full-extension first-order AD/MVT with the separately justified feasible-value upper in LEGAL-CARTESIAN-VALUE-BOUND.md. Physical clips only enter the final value upper, never derivative intermediates. Interval refusal keeps the box. Full 3D subdivision retains both children; all five initial branches are included.

Completed probe:2839evaluations,0live,74illegal+1348value leaves; maximum terminal upper28.10694872459886<28.10695. Source-pinned replay certify_low_corners.py→low_corners_certificate.json must match before registration. This bound is over corner subsets only; stationary arc values, mixedlow/high widths and global nonflat configurations remain separate obligations.
