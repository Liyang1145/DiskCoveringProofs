# Upper quadratic + disk dual: no objective-concavity assumption

Fixed outer parameters r,b1,b2, hubX∈C (convex three-disk lens plus wedge). Objective F(X)=A·X+sum[a_j theta_j(X)+beta_j|X-Q_j|²+gamma_j|X-Q_j|], beta_j>0,gamma_j<0,a_j>0. Coordinate reflection for the rightface is included in theta_j gradients. Select any anchorX0 distinctfrombothQ_j, in C (or use a larger convex domain containingC andX0). Suppose distance |X-Q_j|>=ell_j>0 throughout this convexdomain, and theta_j has a continuoussamebranch there.

1. Normsupport: |X-Q_j|>=n_j·(X-Q_j), n_j=(X0-Q_j)/|X0-Q_j|. Multiplygamma_j<0 to obtain an upperbound. This is global; no square-root approximation or concavity premise.
2. AngleTaylor: theta_j(X)<=theta_j(X0)+g_j·(X-X0)+|X-X0|²/(2ell_j²), since its Hessian operator norm is1/|X-Q_j|². A certifiedpositive lowerell along the entire segment is essential.
3. Thus F(X)<=U(X)=kappa|X|²+B·X+C0,
 kappa=sum(beta_j+a_j/(2ell_j²)),
 B=A+sum[-2beta_j Q_j+gamma_j n_j+a_j g_j-a_j X0/ell_j²],
 C0=sum[beta_j|Q_j|²-gamma_j n_j·Q_j+a_j(theta_j(X0)-g_j·X0+|X0|²/(2ell_j²))].
AtX0 allnormsupport/angleTaylor boundsareequalities; no baseline secanterror. Quadraticenvelopeerror depends ondiameter ofdomain.

4. For any multiplierslambda_i>=0 for diskconstraints |X-C_i|²<=rho_i², set h=sumlambda_i-kappa. If h>0, then onC
 U(X)<=U(X)-sumlambda_i(|X-C_i|²-rho_i²)
       =-h|X|²+d·X+e <= e+|d|²/(4h),
 d=B+2sumlambda_i C_i, e=C0+sumlambda_i(rho_i²-|C_i|²).
This is an explicit global uppercertificate for F on C. Extra boxconstraints can be includedvia nonnegative affine multipliers; no numerical optimizer output is assumedexact. Arbitraryrationalnonnegative lambdas with intervalh>0 suffice. If h=0 andd=0 exactly, upper=e; do not infer exactzero from intervals.

A numerical dualsolver can propose lambdas, followedby directed evaluation. Allformulas hold uniformly in an outerparameterbox if the fullanchor/angle/ell assumptions are certified and lambda chosenfixed. VariablesX0,Q_j,C_i,A may be parameterfunctions; interval evaluation mustretain enoughcorrelation forusefulbounds. No globalridgeassumption, no pertermconcavityclaim, no stationarityrootexhaustion.

Next control: at a fixedouterpointcompare dualupper with numericalprimal and existingintervalscalarfiberupper. The needforpositiveell andcorrectanglebranch is the criticalinterface. Broadglobalell1/50000 is formallyvalid onactualC848 but givesuselesscurvature; usehubnormdisklowerdistance |c_j|-(1-r)>0 or subdividedconvexlens boxes. This doesnot justifypositiveellonanarbitraryrectangularanalyticextension.
