# Explicit angle gap at the common-hub endpoints

Scope as C842: inward q0k4 covers of unitD at allowance r∈[3/8,U], U=37999/100000; endpoints0and4. Strengthening: alpha_i < pi−10^(-8) for both endpoints. No claim for other7sectors, no sharpoptimality.

## Analytic band containment (no sampling)
Let eps=1/100000000. Suppose alpha>=pi−eps and rotate switches toP=(k,h),Q=(k,−h), k²+h²=1,k>0,h>0. Writecenter c=(k−H,y) withH>=0 frominwardnormbound. Widthgapg>0.0466 givesh=sin(w/2)>1/50 (certified chordbound in ten_gap_constants_control.json). Letp=|P−c|,q=|Q−c|<=r<=U. Crossproduct identity
 2hH=pq sin alpha<=U² eps,
using sin alpha=sin(pi−alpha)<=eps. SinceU²<4/25 and2h>1/25, **H<4eps**.
Norm inequality (k−H)²+y²<=1−r² yields
 r²−h²+y²<=2kH−H²<=2H<8eps.
Alsoh<=r followswidth<=2asinr. Therefore
 |y|<sqrt(8eps)<3/10000,
 r−h=(r²−h²)/(r+h)<8eps/(3/8)<3/10000000.
The two endpointdistances satisfy p,q>=h−|y|>r−3003/10000000. AtR0=19/50 normalization,
 p/R0,q/R0 > (3/8−3003/10000000)/(19/50) >493/500.
The final comparison is exactrational: (3/8−3003/10000000)−(19/50)(493/500)=197/10000000>0.
Thus every alleged near-degeneracy is in the explicitbox alpha∈[pi−eps,pi], u,v∈[493/500,1]. This deliberatelyloosebox doesnotneednear-equalityu=v.

## Continuous factor certificate
certify_endpoint_sector_band.py uses the auditedring intervalkernel withfixedR0=.38 andexact9decimalcoefficients, inheritedcomplete29factorbounds fromC842. It partitions each ofu,v into20closedintervals withrationaloutwardendpoints, keepingfullalphaband (400boxespersector). For a=pi boxesmeanvalue atan2shortcutdisabled; directupperenclosurescoveraxes. No gridpoints are used asupperbounds. Allboxescoverentireband. Conditionalringuppers:
 i0 <=−0.04944489422930917573996459567901176094425;
 i4 <=−0.04944492410446785836199447401532450142612.
Allotherfactors unchanged; assembledarea upper:
 i0 <=3.138154920140642127311141964326811317007<pi;
 i4 <=3.138126450986678900813115072187040285917<pi.
Contradiction. Evidence endpoint_sector_band_certificate.json. Exact rationalbandcontainment control check_endpoint_angle_gap.py.

This removes a closed neighborhood ofbothendpointdegeneracies, not onlyalphaπ itself. In compactnecessarydomainC841 imposealpha0,alpha4<=pi−eps safely. Endpointheights then also boundedawayzero usingp,q>=delta/2 andwidthbounds, but currentclaimrecordsanglecutonly. Othersectorsmaystillflatten. Originalsharpinequalityremains.
