# Shape of common-radius sublevel sets

For0<x<1, h(x,b)=atan2(sin b,x−cos b),0<b<π,
 h_b=(x cos b−1)/D,
 h_bb=x(1−x²)sin b/D²>0,
 D=x²−2x cos b+1.
Thus H_x(beta)=Σh(x,beta_i) is strictly convex in beta. Since H decreases in x, onπ<Σbeta<2π,
 x0(beta)<=X iff H_X(beta)<=π.
So x0 has convex sublevel sets (quasiconvex), despite the grouped area not being globally concave. Convexity does NOT authorize an upper tangent to H; tangent is lower. On a rectangular box, secant chords give an upper separable affine bound for H_X, potentially proving larger polytopes have x0<=X than the simple lowercorner box test. This is a possible polyhedral stratification route; no implementation or certificate claim yet.

At X=1, h=(π−b)/2 and Hessian0. At X=0, h=π−b; handle endpoint by limits. The proof uses only exact derivatives, not numeric fitting.
