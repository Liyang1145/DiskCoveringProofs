# Exact joint boundary support has a concave symmetric branch

This sharpens BOUNDARY-AREA-PERIMETER-JOINT.md without replacing caparea by its chordline.
Let b(α)=2asin(r sin(α/2)), z=r sin(α/2), w=sqrt(1−z²), and μ≥0. The symmetric corner branch is

 F(α)=r²sinα/2 +(b−sin b)/2 +μb.

The other corner is the constant g(A)/2+μA, A=2asin(r/2). Separatelyconvex endpointargument proves the maximum of these two bounds every actual wedgearea+μθ.

F'=r²cosα/2 +(z²+μ)b',
F''=−r²sinα/2 +2zz'b' +(z²+μ)b''.

Here b''≤0. Write t=α/2. The positive middleterm is r³sin(t)cos²(t)/sqrt(1−r²sin²t), while the firstterm is−r²sin(t)cos(t). Their sum is nonpositive since r cos(t)≤sqrt(1−r²sin²t), equivalent r²≤1. Thus F''≤0 on[0,π]. Any tangent toF majorizes it globally. The max with the constant corner is certified by separately maximizing the tangent-linear branch and constant-linear branch after subtracting the sitepotential.

No interval grid or optimizer premise is needed. `joint_boundary_exact_cap.py` reevaluates existing rational proposals with this sharper tangent; derivative andvalue use exactintervals. Existing tangency points need not optimize the new support. Candidatecontrol mustremain nonexcluded. Independent Fraction replay pending before any newclaim.

## Explicit derivative/domain and global interface
All primes above mean d/dα, with t=α/2∈[0,π/2]. Precisely b''(α)=−r(1−r²)sin(t)/(2w³)≤0 for0<r<1. Differentiating withrespecttot instead multipliessecondderivativesby4; itdoesnotcontradicttheformula. No t>π/2 calculation belongs tothisdomain.

The exactglobalpartition is π=Σ boundarywedges+Σ pairedfacettriangles (C1199), notfullcellarea plusfacettriangles. Eachwedge hasab sinα/2+g(θ)/2; eachpairedfacettrianglecontribution≤U²sinβ. Per-siteangles sum2π, boundaryownedarcs sum2π. Facetendpoints aretruecircumcenters orboundaryswitches, withinUofbothadjacentsites; zerofanedges passbycontinuity. Alloutwardclipping limits aretakenbeforeimposingU or itscapacitybounds.

Forr<=U, endpointbox[0,r]²⊂[0,U]² directlytransferscornerbound, andpairarear²sinβ<=U²sinβ. Thus no monotonicityoftheoptimizeddualobjective isneeded. IndependentFraction12exactcapnegativeplanespassed. Leadanalyticproofunchanged; membermixedderivative/domainobjectionswithdrawn.
