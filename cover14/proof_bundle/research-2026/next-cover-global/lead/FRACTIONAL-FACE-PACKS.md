# Fractional face packing — analytic extension

Let each dualface f have loss lowerbound L_f(β)>=0 satisfyingΣ_{e⊂f}D_e>=L_f. Choose ANY nonnegative rationalweights w_f withΣ_{f:e⊂f}w_f<=1 for everyedgee. ThenΣ_e D_e>=Σ_f w_f L_f, because each nonnegativeD_e countedatmostonce. This extendsedge-disjointpacks(w∈{0,1}).

Forfixedrationaldualpotentials p_e=y_u+y_v define g_e(β)=U²sinβ−p_eβ. Then
 Σ_e g_e−Σ_e D_e
 <=Σ_f w_f[Σ_{e⊂f}g_e−L_f]+Σ_e(1−Σ_{f:e⊂f}w_f)g_e.
Takingindependent suprema perfacecube andperedgeinterval yieldsvalidupperbound withsameexisting3Dboxkernels. Gainrelativeoldedgeplanes isΣ_f w_f delta_f where delta_f=certifiedfacesup−Σ_{e⊂f}oldedgesup. NumericLPoptimizesweightsONLYasproposal; roundweightsrationalandcheckallcapacityconstraints exactly. No compatibilityofseparateboxmaxima isasserted; separatingmaximaonlyrelaxesupward.

Decisiontest:12closestprovisionalsurvivors comparebestintegralpackvsfractionalLPwithsame300/2000-splitfacebounds. IfLPoptimumfractionalinonlyirrelevantzero-gainfaces, nofullpass. Ifmeaningfulgain, certifyselectedfacepartitionsandweightedintervalsum, independentlyreplayweights+incidences+partitions.
