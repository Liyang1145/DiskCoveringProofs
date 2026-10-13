# A small exact chart for the observed D3 candidate (family only)

Status: algebraic derivation of a candidate-family chart, NOT a global symmetry theorem. Rotate one hub to(a,0), put other hubs at rotations±120°. Let the two high-norm ring centers around this hub be(b,±v); let the third ring orbit consist of t·u(60°+120j). Target radius r. Assume the observed active circumcenters are the outward point(a+r,0) of the hub disk and the inward point(t-r)u(60°) of the middle ring. These are selected branches justified only locally near the saved numeric seed (a≈.27824,t≈.76917,r≈.36110).

## Active HRR face plus shared boundary switch
The high ring pair passes through the boundary anchor(1,0) and the inner hole witness(d,0), d=a+r<1. Both circles radiusr then force the radical-axis midpoint relation
b=(1+d)/2=(1+a+r)/2,
v²=r²-(1-d)²/4,
s²=b²+v²=d+r²=a+r+r².
This follows by subtracting (1-b)²+v²=r² and(d-b)²+v²=r²; no high-order circumradius quotient is needed. Take v>0 locally. Their boundary arc halfwidth β has cosβ=b/s and sinβ=v/s.

## Active HHR face
In axes rotated60°, the two hubs are(a/2,±√3a/2), the middle ring is(t,0), and witness(t-r,0) is at radiusr from all three. Hence
F(a,t,r)=(t-r-a/2)²+3a²/4-r²=0,
equivalently F=t²-2tr-at+ar+a²=0.
The central hub triangle is slack at the saved candidate and is not imposed active.

## Boundary tiling between high and middle ring
The high pair occupies angles[-2β,2β] on S1, because each arc halfwidth equals its central-direction angleβ. The middle ring on direction60° must have halfwidthα=π/3-2β to tile exactly. Thus
(1+t²-r²)/(2t)=cos(π/3-2β)
= (1/2)(b²-v²)/(b²+v²)+(√3/2)(2bv)/(b²+v²).
Let w=√3 v>0. Then all equations can be expressed polynomially over Q:
2b=1+a+r,
4w²=12r²-3(1-a-r)²,
(1+t²-r²)(3b²+w²)=t(3b²-w²+6bw),
F(a,t,r)=0.
Branch guards near seed:0<a<t<1, r>0, v=w/√3>0, a+r<1,0<β<π/6 and0<α<asin r; require all ring centers inner-root and all omitted triangle radii≤r when constructing a cover.

This is a one-parameter contact family in (a,t,r,b,w) before optimization. Local stationarity of r along it supplies one additional polynomial determinant equation (or Lagrange multipliers). A unique isolated root and coverage at that same root still require certified isolation and verification of slack triangles/boundary tiling branches. Global optimality requires the unrelated unrestricted topology and anchor-domain lower bound.
