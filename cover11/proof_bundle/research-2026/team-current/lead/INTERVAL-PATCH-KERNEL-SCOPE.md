# Intervalpatchkernel scope and enclosure argument

Frozen source joint_nested_frozen.json sha2565671967c5a3df341b068975b161900c8b7df4fd59298a4e4fb9f7210438221fb; exactcoefficients9decimal, R0=19/50. Bounds apply ONLYactualinwardflatq0patches lyinginsideinputboxes, not everyunphysicalcoordinate tuple inabroadbox.

## Natural kernel
Actualsectorendpointdistance/R0>=19/100 (INWARD-ENDPOINT-SEPARATION.md, elementary inwardroot bound) and<=r/R0. Actualsectororientedcross andleftbasecross >=0 (triangleorientation). Clipping naturalintervals bythese necessaryranges retains EVERYactualvalue, regardlessofcoefficient signs. It neednotretainunphysicalvalues. atan2(poscross,dot) withnonnegativecross enclosesanglebranch[0,pi]. Atcross=0,dotnegative atan2 includespi; degeneraciesarenotdiscardedunlesswholeboxstrictlyviolatesnecessarypredicate. Physicalpairdistance>1/50000 suppliespositiveQjfloor, facecircumradius<=r givesedge<=2r. These alsoare necessaryrangeintersections, notchanges toobjective. Quadraticlength terms evaluatedaswholepolynomial via endpoints+stationaryvalue, ratherthanseparatesignedproducts; intervalcoefficientsenclosethesamefixedexactcoefficients. Union extrema ofallfixedcoefficients areboundedbecause endpoints evaluatedintervalwise andstationaryvalue formula covers allcoefficientchoices withfixedsigna.

## Fiberprojection
C849givesindependentwidth/Hintervals atfixed4outerparameters. setup() uses outwardupperwidth andoutwardHprojection: lower=max(lowerendpoints ofalllowerconstraintenclosures),upper=min(upperendpoints ofallupperconstraintenclosures). Projectioncontains allactualfibers despiteforgettingparametercorrelations. bminC850 rejectsonlyif entireb interval isbelowentirethreshold; hubdiscriminantrejectsonlyifupper<0. No root sign test basedonfloatnearzero.

## Meanvalueguard
Naturalrawboundvalidonly onactualfeasible subset. It cannotautomaticallybeusedasanalyticcenter forpoints whosemidpoint is infeasible. Hence widthbound's guard provesALLpoints inouterbox ×widthsegment haveinactiveclips(ddlower>=constantupper,ddupper<=r²lower,orientationandlcstrictlypositive). Underthisguard center is genuineanalyticvalueenclosure andderivativeformula validforentiresegment. Withoutguard returnraw; naturalenclosure remainsvalidonactualsubset. The independentmember's claimrawfallbackmustencloseunphysicalpoints wasrejected; this is a scopeerror, not a kerneldefect.

## Bookkeeping
Scalarheap uses midpointupperonly asheuristicthreshold, NOTfeasiblelowerbound. Everyprunedboxupper isretainedin terminal=max(allpruneduppers); finalupper=max(terminal,allliveuppers). A leafrejectedbyfun(None) containsnoactualfeasiblepoint. Childclosedintervalscoverparent includingmidpoint. Budgetstopreturnscurrentupper, neversamplevalue. Outerheapsameinvariant, constant+sumsroundoutwardusingiv thennextafterfloatupper. No concatenationofnumericmaximaintoacertificate.

## Coverage
Broadouterdomain r∈[3/8,R0],bj∈[acosR0/2,acos(3/8)],A∈[0,2acos(3/8)] includesallC849models;B=b1+b2-A clipped[0,pi]. Widths[g,2asinr],H∈[0,2r] includeactualfibers. Actualnondegeneratebranch excludeszeroanglebutclosedenlargement safelyretainsit. NoWLOGsymmetry.

## Calibration/results
1632randomactualpatches: naturalpointinterval versusindependent7atom/reducedsum differenceswithin1.78e-14floatingroundoff; thickboxes enclose everyvalue. Thiscalibratesmap only. Localpointfiber directedupper28.10432600202151 andsmallouterbox28.10432674918808 (meanpass), notglobalupper. Full4D1601box naturalpass29.1114233122; quadraticrangeplusbminpass28.6796137086. Too looseforbelowpiassembly. No flatbranch exclusion. Weightedalternatepass loggedseparately. Historicalquadratickernel reconstructedbyteforbyte asinterval_joint_patch_quad_snapshot.py because lateralternateformulaedit occurredwhileimportedjobrunning; storedhashcorrectedexplicitly, no coefficientchanges.
