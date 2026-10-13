# Boundary viewing-angle capacity — new necessary linear coupling

Let B(c,r) be an inner-normalized boundary disk: |c|²≤1−r², r<1. Along any covered unit-circle arc x(t)=(cos t,sin t), put d=|c| and ℓ(t)=|x(t)−c|≤r. The oriented viewing angle φ(t)=arg(x(t)−c) has derivative

    φ'(t) = (1−c·x(t))/|x(t)−c|²
           = (1−d²+ℓ(t)²)/(2ℓ(t)²) ≥ 1.

Indeed 1−d²≥r²≥ℓ(t)². There is no singularity: |c|<1. Therefore every nearest-owned arc of lengthθ has viewing angle α≥θ. The endpoint chord argument of AREA-SAFE-RELAXATION.md ensures that this is the minor angle in[0,π], not an angle modulo2π.

Since θ_i≤L=2asinr and Σθ_i=2π, every cover additionally satisfies

    Σ_i min(α_i,L) ≥ 2π.

This is equivalent to existence of auxiliary θ_i∈[0,L], θ_i≤α_i, Σθ_i=2π. It is a convex restriction of the safe area relaxation (the min-sum is concave). It couples perimeter capacity with area without the FALSE symmetric-subarc formula θ≤2asin(r sin(α/2)).

Outward clipping obeys the same inner-norm condition; compactness passes this relation to the limit. At U, since L(r)≤L(U), the fixed-U relation remains necessary.

Status: analytic necessary inequality proved as above; proposed next bounded test is to add the auxiliary θ variables and determine whether this removes additional retained graph classes. No new exclusion asserted yet.
