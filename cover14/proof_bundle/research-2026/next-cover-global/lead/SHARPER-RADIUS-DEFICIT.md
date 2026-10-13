# Sharpening edge loss without additional geometric premises

For any real-or-virtual opposite angle pair, write b=β∈(0,π), d=|Δ|≤(π−b)/2 and k=tan(b/2). C1222 givesτ=k tan d and
 D/U²≥2τ sin b/(1+τ)=2(1−cos b)tan d/(1+k tan d).
Since v↦v/(1+kv) increases and tan d≥d,
 D/U²≥2(1−cos b)d/(1+kd)≥c(b)d,
 c(b)=2(1−cos b)/(1+g(b)),  g(b)=(π−b)tan(b/2)/2.
Here0≤g(b)≤1: witht=(π−b)/2, g=t cot t≤1. In factg increases withb because derivative of t cot t is(cos t sin t−t)/sin²t≤0. Thus c(b)≥1−cos b; continuous extensions c(0)=0,c(π)=2.

Forfacef: ΣD_e≥(U²/2)min_e c(β_e)|Σβ_e−π|. Forboxβ_e∈[l_e,h_e], a rigorous lowerboundonmin c is
 min_e [2(1−cos l_e)/(1+g(h_e))].
Thisdoesnotassumemonotonicityofc itself; separate numerator anddenominatorbounds suffice. Ifh_e=π useg=1; otherwise use g(h_e)=(π−h_e)sin(h_e)/(2(1+cos h_e)), orhalfangletrig forstability. Allclosedfaces/zeroβ handledcontinuously.

Boundeddecisiontest: compare same12closest notalreadyexcluded allfacepacks underoldandnewlosswithfixedjointpotentials. Ifmeaningfulnegativegain, exactintervalboxkernel+independentFractionreplay beforefullpass. Thisisstructuralstrengtheningoflossfactor, notmoreprecision.
