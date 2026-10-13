# DISPROVED naive subarc lemma

Exactcounterexample `area_wedge_counterexample.py`, `area-wedge-counterexample.json`: d=sqrt(1-r²), endpointx=(s,-r), endpointyathalfitsnegativepolarangle. BothendpointsinB((s,0),r); centerinner-normalized. Inequalityequivalentto1−cosθ<=r²(1−cosα); exactintervaldifference>0.01092734. Allanglesin[0,pi], sonobranchambiguity. ThisdisprovestheLEADadaptation, notthepaperor14diskcoveringoptimum. Preservefaileddraftbelowfortrace.

# Boundary wedge inequalities — analytic proof draft

Let |c|=d≤sqrt(1−r²), r<1/2, and x,y lie on S1 within B(c,r), in their cyclic shortarc oflengthθ. The rays c→x,c→y span angleα∈[0,π]. Define f(α)=2asin(r sin(α/2)) and F(α)=(f(α)−sin f(α))/2+(r²/2)sinα.

Claim θ≤f(α) and wedgearea≤F(α). This isFejesToth2005's boundaryfunctioninequality; actualendpointsneednotlieon∂B(c,r).

Usecoordinates c=(d,0), x=(cos t1,sin t1),y=(cos t2,sin t2). Letψ(t)=arg((cos t−d)+i sin t), continuous on visiblearc |t|≤tmax. ψ'(t)=(1−d cos t)/(1+d²−2d cos t)>0; ψ''(t)=−d(1−d²)sin t/(1+d²−2d cos t)². Thusψ' decreasesfor t>0 (and iseven). Consequently forfixedθ=t2−t1, theangleα=ψ(t2)−ψ(t1) isMINIMIZED whenintervalis pushedtooneendofactualcoverarc, NOTwhen symmetric. This observation warns againstclaimingisoscalesmaxθforfixedαwithoutadditionalargument.

Alternativeuse radialdistancesu=|x−c|,v=|y−c|≤r. Theoriginandc lieonthesamesideofchordxy: sincec·x,c·y≤d<1 andarc endpointswithincovercap, actuallyneedcheckchordside via d cos(midangle)≤cos(θ/2). Innernormd≤sqrt(1−r²) andθ≤2asin r give d≤cos(θ/2), soyes. Thetrianglecxy angleα lies≤π andhasc behindchord. Relatecirclegeometry: withmidpointangleφ andhalfθ=h, horizontalchordnormaln, set A=cos h−c·n≥0, B=c·tangent. Rays toendpoints (A,±sin h−B), with squaredlengths≤r². Theircross=2A sin h, dot=A²+B²−sin²h. Theinnernorm conditionA²? d²=(cosh−A)²+B²≤1−r² gives
2A cosh≥A²+B²+r²−sin²h.
Alsoendpointconstraints A²+(|B|+sin h)²≤r².
Needdeduce sin h≤r sin(α/2), equivalently cosα≤1−2sin²h/r². Generaltrianglewithu,v≤rdoesNOTimplythisforsmallα; butinnernorm inequality mayforceit. Deriveordisprovebeforeusingarearelaxationascertificate.

Areaformula exact: wedge = (θ−sinθ)/2 + uv sinα/2 ≤ (θ−sinθ)/2+r²sinα/2. Thusifθ≤fα establishedandα∈[0,π], area≤Fα followsmonotonicityθ−sinθ. Concavityf,F supportedbyliteraturebutmustrederiveorcorrectlycite, withendpointinequalitychecked.
