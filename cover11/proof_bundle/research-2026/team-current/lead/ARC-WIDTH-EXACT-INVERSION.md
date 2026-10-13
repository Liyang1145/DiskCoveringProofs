# Correct exact arcwidth inversion (lead proof)

C849 setup: r∈[3/8,R0], alpha=acosr,b∈[alpha/2,alpha],x=2b-alpha∈[0,alpha]. Directexpansion gives X=r sinx,D=1-r cosx>0, soW=2atan2(r sinx,1-r cosx). Its derivative wrtx is
 dW/dx=2r(cosx-r)/(1-2r cosx+r²)>=0,
 strictlypositiveforx<alpha. ThusW maps[0,alpha]bijectivelyonto[0,2asinr].

For0<=g<=2asinr writeeta=g/2. The equationW=g is equivalent (sinceallanglesonpositiveprincipalbranch) to r sinx coseta=(1-r cosx)sineta, i.e.
 sin(x+eta)=sineta/r.
The increasingarc branch yields the UNIQUE solution
 x_min=asin(sineta/r)-eta,
 **b_min(r,g)=[acosr+asin(sin(g/2)/r)-g/2]/2**.
Branchjustification: atthissolution x+eta=asin(sineta/r)<=pi/2 and x∈[0,alpha], withx=alpha onlyifeta=asinr. HenceW>=g iff b>=b_min. Also b_min decreasesstrictlyinr atfixedg<2asinr, sincebothacosr andasin(sineta/r) decrease; differentiating gives
 db_min/dr=−1/(2sqrt(1-r²))−sineta/[2r²sqrt(1−sin²eta/r²)]<0.
This suppliesa single uniform lower b boundb_min(R0,g), strongerthanacosR0/2. g here=2pi−16asinR0; g<2asin(3/8) confirmedtriviallyviaoutwardinterval ormonotonictriginequality; codecontrolstoresintervalcheck.

Equivalenthalfanglequadratic t(1+r)z²−2rz+t(1−r)=0, t=taneta,z=tan(x/2). Itsdiscriminantis4[r²−(1-r²)t²], NOT4(r²−t²). Stable root z=t(1-r)/(r+sqrt(r²−(1-r²)t²)). Avoidtheincorrectmemberreportv1 whichalso usedxupperpi-alpha. Leadproofaboveauthoritative.
