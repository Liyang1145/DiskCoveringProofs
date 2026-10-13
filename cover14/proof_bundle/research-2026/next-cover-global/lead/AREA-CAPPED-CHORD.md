# Joint capped-affine perimeter capacity

C1208's tighter rational envelope θ≤A+kα uses A=.333272257,k=.123099267, with constants independently certified. Also θ≤L(U)<Lbar=.676277969. Hence

    Σ_i h(α_i)≥2π,   h(t)=min(Lbar,A+kt), 0≤t≤π.

Here h is concave and its sole breakpoint T=(Lbar−A)/k lies in(0,π), checked exactly. This is equivalent to existence of θ_i∈[0,Lbar], θ_i≤A+kα_i,Σθ=2π. No false symmetric owned-subarc formula is used.

For any rational μ≥0, add μ(Σh−2π)≥0 to the area objective, hence obtain a valid UPPER bound on its maximum. After the usual sin supportingplane and sitepotential correction, boundary coordinate j with slope b_j contributes at most

    max( μA, T b_j+μLbar, π b_j+μLbar ),

because b_j t+μh(t) is piecewise linear with breakpoints0,T,π. Interior-edge coordinate contributes πmax(0,b_j). Constant changes by−2πμ. Every maximum is evaluated with directed intervals; rational proposals need not optimize anything.

`area_capped_chord_catalogue.py` evaluated this stronger relaxation once on all1130 C1208 survivors; it removes44 more (20q10m4,24q11m3), retains1086=366q10m4+720q11m3. `area-capped-chord-catalogue.jsonl` storesplanes, metadatahashes in matchingJSON. Independent exactFraction replay of12boundedcontrols and ALL44newexclusions passed; area-capped-chord-catalogue-fraction-replay.json.

This is modest additional pruning, not a reason to increase precision or grids. Next structural obligation: characterize the sharp boundary viewing-angle envelope using the innernorm constraint |c|≤sqrt(1−r²), which the endpoint-corner envelope discarded. This geometry could remove the large artificial plateau and tighten allgraphsystems at once.
