# Smooth-angle continuation and exact cancellation of joint objective

Let phi=asinr,s=sqrt(1-r²),alpha0=acosr. For each adjacent b∈[alpha0/2,alpha0], c=(s−2r sinbcosb,−2r sin²b), P1=(s,−r),P(w)=clockwise rotationofP1.
Define p=c·P,x=cross(c,P),eta=atan2(x,1-p).
Directcomplexargumentgives eta=arg(P-c)−argP, takingthebranch(-pi/2,pi/2). Indeed |c|²=1+r²−2r sin(2b+phi)≤1−r², hence1-p≥1−sqrt(55)/8>1/14 forr∈[3/8,19/50]. Thelastcomparisonisequivalentto2704>2695. Thuseta smoothforALLrealw, noflatendpointbranchcut.
Endpointeta1=2b+phi−pi/2. Thephysicalsectorangle andleftbaseangle obey
 alpha=w+eta1−eta, L+w/2=pi/2+eta.
Theseexpressions areanalyticcontinuations outsidephysicalrangealpha≤pi; objectivecenterneednotbephysical. Allsqrt/atan2Hbranchesstillrequireexplicitintervalguards.

Let mu1=z1,mu3=z3,h1=z112,h3=z115,d1=z34,d3=z39,l1=z96,l3=z101,delta=b1−A (B=b2+delta). InC849separatedformula, substitutingalpha above andcombiningtheK terms EXACTLY gives
 J=Cpi+(1−mu1−mu3)phi+(mu3−mu1)delta−rs(sin²b1+sin²b2)
   +sum_j[(1/2−muj)wj+xj/2+(muj+hj)etaj−dj uj²−lj uj]+FH,
 Cpi=pi(z113+z114−z2)+(pi/2)(h1+h3−mu1−mu3),
 uj=|P(wj)−cj|/R0,
 FH=sum_j[H Dj sinθj/2+aj atan2(Dj sinθj,H−Dj cosθj)+betaj Lj²+gammaj Lj],
 withDj=2r sinbj,theta1=A,theta3=B,Lj=sqrt((H−Djcosθj)²+(Djsinθj)²); coefficientsasH-STATIONARY-POLYNOMIAL.md.

Cancellationproof: each−muj alpha contributes−muj(2bj+phi−pi/2); K contributesmuj(2bj−pi∓delta). Theycancelbj andleave−muj(phi+pi/2)∓mujdelta. Boundaryarea suppliesphi−rs. Thetwo sitearea termsr²sin2bj/2 combinewith−X1j/2 usingX1j=r²sin2bj−rs cos2bj, givingrs cos2bj/2; summingandcombining−rs yields−rs sumsin²bj. No inequality introduced.

This is a scalaranalyticidentity for the SAMEzeroangleinequality-multiplier frozenobjective; notnewphysicalconstraint, notcertificate. It removesopposinglinear bj terms andarea/crosscancellations beforeintervalAD, ratherthanexpectingnaturalintervalarithmetic todiscovercorrelation.
