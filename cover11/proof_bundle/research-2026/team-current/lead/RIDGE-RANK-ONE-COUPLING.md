# Ridge-only objective: rank-one concave coupling (analytic representation)

Scope frozen C849 objective restricted to delta=b1-b2,H=2r sin(b1+b2); r∈[3/8,.38], bj∈[1,acos r]. This does NOT assert all maxima lie on ridge.
Let t=r/R0, a1=z1-z9,a2=z3-z9. Let Wj(r,bj,wj) be the scalar width function from cartesian_full_jet.py (including -r sqrt(1-r²) sin²bj). Then exact ridge objective:
G=K(r)+F1(r,b1,w1)+F2(r,b2,w3)-r² sin(2(b1+b2)),
F1=W1+r²sin2b1+(z3-z9)b1+z20*t² sin²b1+z82*t sinb1,
F2=W2+r²sin2b2+(z1-z9)b2-z16*t² sin²b2-z78*t sinb2.

Proof: 4sin(b1+b2)sinb1sinb2=sin2b1+sin2b2-sin(2(b1+b2)); delta-linear term cancels with hub-angle terms to the displayed swapped coefficients. All other terms are already independent in (bj,wj).

Structural consequence: T=b1+b2∈[2,2acos(3/8)]⊂(pi/2,pi). h(T)=-sin2T has h''(T)=4sin2T<0 throughout this interval (2T∈(pi,2pi)). Thus for ANY fixed tau in the interval,
h(T)≤h(tau)+h'(tau)(T-tau)=-sin2tau-2cos2tau(T-tau).
Multiplying by positive r² preserves it. Ridge G is bounded above by
K(r)+r²[-sin2tau+2tau cos2tau]
 + [F1-2r²cos2tau*b1]+[F2-2r²cos2tau*b2].
The maxima of these two bracketed terms separate at fixed r; legal width fibers remain conditional on their own b only (C849). One constant tangent tau near candidateT yields a global upper bound on the whole high-bearing ridge; an infimum over tangents may tighten it. Tangent coefficients must be outward interval evaluated, not numerically fitted as exact.

Next executable obligation: calibrate decomposition/tangent against saved candidate and offcandidate points; bound each (b,w) component using full-term AD/MVT preserving cancellations. This removes one coupled bearing parameter rather than refining the old 5D ridge grid.
