# Boundary endpoint cone from innernorm — analytic draft

At normalizedradius r, allsites|c|<=s=sqrt(1−r²). For anyunitanchor A, vectorsc−A pointwithinaninwardradialconeofhalfangleasin(s)=pi/2−asin(r). Let adjacentanchorB haveownedarc theta∈[0,2asin r]. VectorB−A makesangle pi/2−theta/2 with−A. Sitec liesoninnersideofchordAB, soendpointtriangleangle delta betweenB−A andc−A is nonnegative and
 delta >= asin(r)−theta/2.
Thisfollowsangulartriangleinequality evenwithoutsideassumption; sideassumptionfixesprincipaltrianglebranch. Also delta<=pi−asin(r)−theta/2 ontheinnerradialcone withorientation. Both endpointangles satisfybounds, consistentwithdelta1+delta2=pi−alpha.

At sharedanchorA withadjacentownerarcs theta_u,theta_v andvirtualgammaA, cyclicitygives2gammaA+delta_u+delta_v+(theta_u+theta_v)/2=pi. Thus
 **gammaA <= pi/2−asin(r)=acos(r).**
Equivalently atboundaryedge uv theunitanchoranglebetweenAu,Av <=2acos(r), alreadyimplied bybothsites lyingininwardradialcone. Radiusinterface:
 gammaA=h(y,x,beta), hence x sinbeta/(y−x cosbeta)<=cot(asin r)=sqrt(1−r²)/r,
 so **y >= x(cosbeta + r/sqrt(1−r²) sinbeta)** (denominatorpositive; if RHSnegativeautomatic).

CAUTION monotonicthreshold: r<=U makesasin(r)<=asin(U); cannotreplaceconstantbyU forglobalcovers. But normalizedsites canpotentiallyrenormalizeatU: originalsitesnorm<=sqrt(1−r²) NOTsqrt(1−U²). Needapplysame-arc innerrootnormalizationatU anew sincecoveratU, retaining a possiblydifferentgraph; C1171 atfixedU admissible. Thisrequirescheckingfinitecataloguenecessity formulation for coveratr<U upgradedtoU andthenrenormalizedatU. Existingglobalclaimnecessity allr<=U maynotpreservesamegraphunderthisoperation; newproofmaytakeanewnormalizedgraph (existential suffices). Alternatively useweakeruniformboundr>=knownlowerbound (e.g area r>=1/sqrt14), yielding gammaA<=acos(1/sqrt14), no graphchange.

Next bounded LP/interface test shoulduse exactsafeL=1/4 (<1/sqrt14) orglobalarea lower1/sqrt14, notsilentlyplugU. Thisnoteunregisteredpendingorientationaudit.
