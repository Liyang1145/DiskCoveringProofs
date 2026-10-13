# Degree-eight equation for every interior width-fiber stationary point

Continue C849. Fixed actualr,b and neighborcenterc, P(w)=clockwiserotation(P1,w). Let d0=c·P1>0,x0=cross(c,P1)>0, C2=|c|². Widthobjective is F(w) of JOINT-PATCH-SEPARABLE-FIBERS.md; coefficients mu,h,d,l are fixed realnumbers fromdual. R0=19/50; k=-mu-h. Write p=c·P(w), x=cross(c,P(w)), D=|P(w)-c|²=1+C2−2p>0. Then
 F'(w)=(1-p)/2+k(1-p)/D+h+(2d+l R0/sqrtD)x/R0².
Multiplying by2D gives
 2D F'=A+2l x sqrtD/R0,
 A=D(1-p+2h)+2k(1-p)+4d D x/R0².

Set y=tan(w/2), Q=1+y²>0. For clockwiseorientation:
 Pnum=d0(1-y²)+2x0 y, Xnum=x0(1-y²)−2d0 y,
 Dnum=(1+C2)Q−2Pnum.
Thus p=Pnum/Q,x=Xnum/Q,D=Dnum/Q. Define the degree<=4 polynomial
 Anum=Dnum*((1+2h)Q−Pnum)+2k*(Q−Pnum)*Q+4d Dnum Xnum/R0².
Every stationarypoint therefore satisfies the polynomial ofdegree<=8
 **G(y)=Anum²−4l² Dnum Xnum² Q/R0²=0**,
in the explicit interval y∈[tan(g/2),tan(W/2)]. Squaring can add roots: retain only roots satisfying the original unsquared derivative equation; if using only an upperbound, evaluate everyroot safely, includingextraneousones. Endpoints mustalso beevaluated. If G is identicallyzero, do NOT claim finitelymanyroots; use unsquaredderivativeanalyticcase orordinaryintervalbounding. WithnonzeroG thereareatmost8 realstationarycandidates, countedwithoutmultiplicity. Allfunctionsare smooth inwidth sinceD>=R0²*(19/100)²>0 onactualpatch domain.

This yields an algebraic univariate extremum representation atfixedouterparameters, not an outercontinuumcertificate. Coefficientsdepend onr,b viaanalyticfunctions; theyarenotfixedrationalnumbers globally. Parameterintervalrootmethods musthandlecoalescence/rootentry atfiberendpoints, nottrackonlyroots atonepoint.
