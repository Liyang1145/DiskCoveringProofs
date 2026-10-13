# New structural obligation: boundary area/perimeter joint support

Status: analytic reduction draft, no new graph exclusions. Unlike the earlier bounds, this retains the penalty in triangle area for unequal endpoint lengths.

For one owned arc with endpoint distances a,b∈[0,r] from its site and viewangle α∈[0,π], let d=sqrt(a²+b²−2ab cosα), θ=2asin(d/2), g(θ)=θ−sinθ. Exact wedgearea is ab sinα/2+g(θ)/2.

For any multiplier μ≥0, its area-plus-perimeter value is

 F(a,b)=ab sinα/2+g(2asin(d/2))/2+μ·2asin(d/2).

As a function of d∈[0,2r], the last two terms are convex and nondecreasing: d↦2asin(d/2) is convex increasing, and θ↦g(θ)/2+μθ is convex increasing on[0,π]. Also d is a norm of an affine function of(a,b). Thus the last terms are jointly convex in(a,b); the first term is separately affine. F is separately convex, so its maximum over[0,r]² is at a corner:

 F≤max( r²sinα/2+g(b_r(α))/2+μ b_r(α), g(A_r)/2+μ A_r ),
 b_r(α)=2asin(r sin(α/2)), A_r=2asin(r/2).

This statement does NOT assume equalendpointdistances; the unequal corner(a,b)=(r,0) is retained, but its trianglearea isZERO. The previous relaxation incorrectly combined the best area from one corner with the best perimeter from the other (valid upperbound, but loose). Here that loss is repaired.

For a valid cover, Σθ=2π and area=π. Therefore for arbitrary μ≥0,

 π+2πμ ≤ Σboundary max( r²sinα/2+g(b_r(α))/2+μ b_r(α), g(A_r)/2+μ A_r ) + Σedges r²sinβ.

The site angleconstraints persist. To obtain rigorous graphwise upperbounds, combine sitepotentials with analytic/interval coordinate suprema onα∈[0,π], β∈[0,π]. The maxbranch is not generallyconcave. Need develop a verified univariate support calculation, not trustSLSQP maxima. At this stage no implementation or exclusion is claimed.

Possible simplification: replace g(θ)/2 by its chordline γθ, γ=(L−sinL)/(2L), θ≤L. Then each boundarybranch becomes either r²sinα/2+(μ+γ)b_r(α) or(μ+γ)A_r. The first is concave inα and the second constant. A tangent to the first plus a max with the constant is an exact piecewiseaffine upperbound, allowing the same box endpoint certificate. This version trades some sharpcap gain for the crucial area/perimeter coupling; compare on knowncandidate before cataloguework.
