# Exact height-cone chart for all C848 fibers

Domain: r∈[3/8,19/50], b1,b2∈[acosr/2,acosr], A,B>0,A+B=T=b1+b2. D=b1−b2, epsilon=delta−D, delta=b1−A. Then A=b2−epsilon,B=b1+epsilon, and positivity gives−b1<epsilon<b2. Also delta∈(−b2,b1)⊂(−pi/2,pi/2). These bounds prevent the alternate arcsin branches mentioned in member C853-CONE-IDENTITY.md: onTHISlegalchart separation is globally |delta|≤u, not a piecewise ambiguity.

C848 face constraints forH>0: H≤2r sin(T−epsilon),H≤2r sin(T+epsilon). Their minimum is2r sin(beta−|epsilon|), beta=min(T,pi−T)∈(0,pi/2]. Sinceepsilon∈(−pi/2,pi/2), nonemptyH requires |epsilon|<beta. (Equivalently, faceargumentspositive and<2pi; positivesineforces(0,pi).) Introduce u=asin(H/(2r))∈(0,pi/2]; then the TWO face inequalities are EXACTLY |epsilon|+u≤beta, coveringbothacute/obtuseT andtheT=pi/2interface. Noactivefaceassumption.

SeparationH≥2r|sindelta| becomes |D+epsilon|≤u. Hubnorm becomes
 cos(D+epsilon)≥q(r,u):=[4r²sin²u+2r(1−r)]/[4rs sinu].
 Rejectq>1. Elseq>0, so |D+epsilon|≤acosq. Thus forfixed(r,b1,b2,u), theENTIREadmissibleepsilonfiberisoneinterval:
 max(−beta+u,−u−D,−acosq−D,−b1) ≤epsilon≤ min(beta−u,u−D,acosq−D,b2),
 withstrictA/Bboundariesexcludediforiginalpositiveanglesrequired. Includingtheclosureissafeupperrelaxation. AllC848constraintsaccounted; H determinedby2r sinu. Domainfiberisemptyiffleft>right, modulooriginalstrictendpoints. This replacesintersectionoffoursinusoidalHconstraints byexplicitlinear/acosbounds inoneangularfiber.

Uniformheightfloor: hubnorm andtriangleinequalitygiveH≥s−(1−r). Forr<5/13, s>1−r/5 (squarebothpositivesides: r(2/5−26r/25)>0); ourr≤19/50<5/13. ThusH>4r/5 andu>asin(2/5). Thisboundjustifiestheouteru-domain[asin(2/5),pi/2]. Physicaledgesseparation/closureconstraintsbeyondC848remainnecessaryadditionalfilters, notprovedsufficientforactualcover.

C849widthfibersdependonlyon(r,bj), so thesamejointobjectivehas4outer(r,b1,b2,u)+3scalarfibers(w1,w3,epsilon). No objectiveoptimality claimed. interval_height_fibers.py implementsoutwardprojectionoftheseexactranges, plusoldsitedistancefilters. check_height_fibers.py calibrated104pointsagainstoriginalindependentscalaroptimizer; calibrationnotcontinuumproof.
