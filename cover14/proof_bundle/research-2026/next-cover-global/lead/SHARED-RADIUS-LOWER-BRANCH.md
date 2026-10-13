# Sum beta < pi: central radius saturates

Fix beta_i∈(0,pi), B=sum beta_i<pi. Localinterface hasx=R/U,y_i=T_i/U∈(0,1], gamma_i=h(x,y_i,beta_i)=atan2(y_i sin beta_i,x−y_i cos beta_i), sum gamma=pi. ObjectiveA/U²=x sum y_i sin beta_i.

## Exact reduction: maximal area has x=1
Take any feasiblex<1 andincreasexto1 whileholdingy. Eachgamma strictlydecreases, hence sumgamma<pi. Atall y_i=1 andx=1 sumgamma=(3pi−B)/2>pi. Interpolateeach y_i upwardto1 simultaneously: sumgamma iscontinuous strictlyincreasing unlessalreadyall1, so thereexistsnondecreasedvector y'_i>=y_i withx=1,sumgamma=pi. Area strictlyincreasesbecausexgrewandnonnegativeygrew. Thereforeglobalmaximumoverlocalcompactclosureattainsx=1 (degeneraciescoveredbylimit).

Then set m_i=(pi−beta_i)/2. Legal gamma_i∈[0,m_i], sum gamma=pi; y_i=sin gamma_i/sin(gamma_i+beta_i). Exact areaoptimizationreduces2D:
 max ΣF_i(gamma_i), F_i(g)=sin beta_i sin g/sin(g+beta_i).
 F'_i=sin²beta_i/sin²(g+beta_i)>0,
 F''_i=−2sin²beta_i cos(g+beta_i)/sin³(g+beta_i).
EachFchangesfromconcaveto convexwhen g+beta crossespi/2. So NOglobalconvexassertion. Ifall beta_i>=pi/2 thebranchB<piisempty; mixedsmallbeta casesmustbehandled.

Equivalent deficits d_i=m_i−gamma_i>=0 withΣd=(pi−B)/2. Atcandidate-tightfacesB=pi onlyd=0andally=1. Slightlybelowpi, allgamma+beta≈(pi+beta)/2>pi/2, givingconvexobjectiveinavailabledeficit-simplexprovided each d_i<beta_i/2. A sufficientfullsimplexcondition is(pi−B)/2<=min beta_i/2, i.e. B+min beta_i>=pi. Then all F_i convex on ALL feasible domain (g>=m_i−(pi−B)/2), so maxatpolytopevertex. The simplex upper bounds d_i<=m_i are automatically redundant, since totaldeficit=(pi−B)/2<=(pi−max beta_i)/2=min m_i. Hence verticeshaveall deficitononeedge; other2neighbor radiisaturate. This gives an exact finite branch representation on a substantialnear-tightregion; thresholdsandtiesneedexplicitclosedhandling.

No certificate usingthisreductionyet. It complementsC1227 upperbranch, ratherthanassumingglobalAconcavity.

## Exact finite formula on B<pi, B+min beta>=pi
Write d=(pi−B)/2. Putting all d on edgei gives y_i=cos(beta_i/2+d)/cos(beta_i/2−d), other y=1. Thus
 A_max/U² = sum sin beta − min_i [2 sin beta_i sin(beta_i/2) sin d / cos(beta_i/2−d)].
Denominatorpositive: 0<=d<=min beta/2 onthisregion, and0<beta_i/2<pi/2. FormulaextendscontinuouslytoB=pi giving0loss. NumericactualcandidatecontrolfourB<pi facesfitsbutdoesNOTattainlocalmax: theirdeficitslieonlarger-costedges (`lower-branch-envelope-control.json`). This indicatesneighboringface consistencywouldstrengthenlocalenvelopesfurther.
