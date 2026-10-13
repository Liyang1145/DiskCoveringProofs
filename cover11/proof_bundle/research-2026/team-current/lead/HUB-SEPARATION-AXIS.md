# Low-bearing stationary geometry: separation-axis representation (work in progress)

For Q1=(r sin2b1,2r sin²b1), Q2=(r sin2b2,-2r sin²b2), set d=|Q1-Q2|, e=(Q1-Q2)/d and n=(e_y,-e_x). The linear coefficient A=(r(sin²b1+sin²b2),r(sinb2cosb2-sinb1cosb1)) is EXACTLY (d/2)n. This removes an apparent independent vector parameter.

Write X=(Q1+Q2)/2+x n+y e, u1=y-d/2,u2=y+d/2, Lj²=x²+uj², Wj=2betaj-cj/Lj. The rotation (n,e) preserves orientation; atan terms have opposite chirality sigma1=-1,sigma2=+1. Therefore

F_x=d/2+(W1+W2)x+a1*u1/L1²-a2*u2/L2²,
F_y=W1*u1+W2*u2-a1*x/L1²+a2*x/L2².

The curvature in the separation direction is
F_yy=2(beta1+beta2)-x²(c1/L1³+c2/L2³)+2*x*(a1*u1/L1⁴-a2*u2/L2⁴).

On legal face constraints Lj<=2r<=.76, both Wj<0 (needs directed constant check before a claimed uniform theorem). A stationary point has its perpendicular offset x constrained by F_x=0. The numerical roots found so far have positive F_yy, even when their Laplacian is negative. Goal: exploit these simultaneous equations to prove positive curvature or bound all remaining stationary points, rather than demand global subharmonicity.

Current status: analytic coordinate/derivative identities; NO proof all stationary points have positive curvature. Existing exact global distance threshold C862 still applies. Numerical diagnostic15roots all saddles is not root completeness. New parameterized Krawczyk root contractor evaluates F at outer-variable intervals and fixed hub midpoint, retains all roots; no existence/uniqueness assertion.
