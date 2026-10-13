# Inward center norm retained as a local sector constraint

Object: any actual inward nearest sector at allowance r∈[3/8,U], with unit-circle switchesP,Q,full widthw∈(0,pi),endpointdistancesp,q<=r,sectoranglealpha∈(0,pi]. FixednormalizationR0=.38 is merelylengthunits; do NOT assertcenter norm<=sqrt(1−R0²). Let h=sin(w/2),k=cos(w/2),P=(k,h),Q=(k,−h),c=(k−H,y),H>=0. Then
 p²+q²=2(H²+h²+y²), 2hH=pq sinα,
 |c|²=1−2h²+(p²+q²)/2−2kH
       =1+pq cosα−k pq sinα/h.
Hence exact equivalence (h>0):
 **|c|²<=1−r² iff pq sin(alpha−w/2)>=r² sin(w/2).**
This is a local necessary inwardnorm constraint, not already included by mere sectortriangle geometry/width formula.

Writeu=p/R0,v=q/R0, h=R0 sqrt(u²+v²−2uv cosα)/2. The actual family necessarily satisfies
 **uv(k sinα−h cosα)>=(r/R0)²h >=(75/76)²h**.
Furthermore r>=max(p,q), so
 **uv(k sinα−h cosα)>=max(u²,v²)h**.
Combining: left >= max((75/76)²,u²,v²)*h. This last condition is a SAFE necessary relaxation, eliminating actualr without imposinginwardrootatR0. Retainalloldfactorbound domains and simply discard boxes whoseleftupper<rightlower. No replacementofmeanvaluegradients or partialcontraction required; intervals acrossconstraint still usefullboxfunctionenclosure. Uniformpairbounds ensurep,q,h>0 onactualcovers; qmin givesh>0 inremainingrelaxation.

Atalphaπ, condition reduces uv>=max(tmin²,u²,v²), forcingu=v>=tmin. This recovers exactdegeneratecornersegment for ANY sector, without manually assuming equality. It can eliminate old independent-ring maxima with radically unequalendpointradii. On ordinarypositive sectors it encodes the radiusbudget missed by usingonlywidth andtriangle constraints.

Scope caution: statementforactualinwardcoversandtheirlimits. Not everyformalC835metric hasinwardcenters, so this is anecessary-domainrestriction viaC837, not a universalidentityofallformalangles. No sharpbound yet. Next test: newfilter on existingfixeddual sector2max; if structuralgain enough, usefullintervalcertificate. No need reoptimizeallmultipliers beforecheckingthis interface.
