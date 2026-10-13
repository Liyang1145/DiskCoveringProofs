# Global geometric feasibility of the face-switching ridge (not objective optimality)

C848/C849 flat-sector patch, actualr∈[3/8,19/50],alpha=acosr,s=sqrt(1−r²), independentlybj∈[alpha/2,alpha]. Let T=b1+b2,D=b1−b2. Setdelta=D,A=b2,B=b1,H=2r sinT.

1. Allfaceanglesvalid: bj∈(0,pi/2), T∈[alpha,2alpha]⊂(0,pi). C848faceHupperboundsbothH exactly. H≤2r.
2. Bothlowerchordconstraints: sinT−|sinD|=2cos(max(b1,b2))sin(min(b1,b2))>0. ThusH>2r|sinD|.
3. Hubnormquadratic N=H²−2s cosD H+2r(1−r). Divideby2r andputv=sinT,c=cosD:
 N/(2r)=1−r+2rv²−2scv.
 Uniformrationalbounds: s>23/25 (since1−(.38)²>.92²); |D|≤alpha/2 impliesc≥sqrt((1+r)/2)≥sqrt(11)/4>41/50. Further sinT≥sin2alpha=2rs≥69/100, andsinT≤1. Therefore
 N/(2r)≤q(v):=5/8+(19/25)v²−(943/625)v.
 q isconvex, so onv∈[69/100,1] itisboundedabovebymax(q(69/100),q(1)). Exactvalues q(69/100)=−13559/250000=−.054236, q(1)=−619/5000=−.1238. HenceN/(2r)≤−13559/250000<0 uniformly.
 Thus H liesstrictlybetween thetwohubnormquadraticroots s cosD±sqrt(s²cos²D−2r(1−r)); discriminant automaticallypositive. This provesallC848Hconstraints simultaneously without numericalsampling.

Consequence: foreachlegalr,b1,b2 (includingallC850width-admissiblepairs), thedelta/Hfiber contains a switchingridgepoint. Widthsindependentandunchanged. This isGLOBALovertherelaxedflatpatchbearingdomain, notaglobaln11theorem,anddoesNOTsayfrozenobjectivealwaysmaximizedonridge. C853stillneedsderivativeconditionsforoptimization; no symmetryWLOG. NecessaryrelaxationfeasibilitydoesnotguaranteeactualpatchgluingorsitedistanceconstraintsbeyondC848.
