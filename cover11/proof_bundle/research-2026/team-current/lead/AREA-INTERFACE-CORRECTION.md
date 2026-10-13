# Solo continuation: area-interface correction

The area_fan_probe / area_degree3 optimizer is NOT a valid covering exclusion kernel as written. Before certification, local geometry exposed an invalid boundary-angle inequality.

Let c=(.8,0), r=.38, boundary endpoints u(.28),u(.35). Both endpoints are inside B(c,r) (distances approx .319861,.370140); c is a valid inward-root center. Their actual center angle alpha≈.1416048, but their boundary angle w=.07 exceeds f(alpha)=2asin(r sin(alpha/2))≈.0537714. Thus assigning every actual nearest-cell boundary sector the inequality w<=f(alpha) is unjustified; skew endpoints have unequal distances to c. This is a numeric diagnostic counterexample, sufficient to flag the instrument, not yet an exact certified artifact. No bearing theorem was registered from the optimizer.

Repair independent of special arc geometry: if a,b<=r are endpoint distances and alpha∈[0,pi], chord²=a²+b²−2ab cos(alpha) is convex in each variable separately, hence max at a,b∈{0,r}. Thus chord<=r max(1,2sin(alpha/2)). For alpha>=pi/3 the original bound is valid; for small alpha replace it by w<=2asin(r/2). Sector area is exactly .5 ab sin(alpha) + (w−sin w)/2, hence bounded by .5r²sin(alpha)+segment(w_max). Need global majorants valid for all alpha before any optimizer certificate.

Fejes Toth published inequality may rely on additional original-cell structure; do NOT claim a literature theorem disproved. This only shows the imported inequality was not established on the current broader cell domain.

Original target remains unchanged. New solo goal goal-111c8863-2da2-42e5-9498-2bd7de377ddf, cap999, no subagents authorized. area_degree3.py has now run: all nine numeric maxima below pi, but they use the invalid interface and carry no exclusion conclusion.
