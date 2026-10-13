# Robust one-hub reduction for a neighborhood of coincident hubs

Scope: fixed radiusU,10 normalized ring disks,2 inactive hubs h1,h2, separation d≤2δ (δ an explicit positive rational to be certified). Core radiusa=1−2U. This avoids singular exposed-union angles atd=0 and removes an actual positive-width region if its independent capacity inequality passes.

Put m=(h1+h2)/2. B(h1,U)∪B(h2,U)⊂B(m,U+d/2)⊂B(m,U+δ). Since the core is covered by the hub union, B(0,a)⊂B(m,U+δ), whence e=|m|≤3U−1+δ. If4U−1+2δ<1, the containing disk B(m,U+δ) lies inintD. Every point on its radiusR=U+δ circle is a limit of points outside both hubs but insideD, hence belongs to the closed union of10 ring disks. They also coverS1. The required circles are nowS1 andS(m,R), for e∈[0,3U−1+δ].

For ring c=ρuφ, ℓ=|c−m|, its inner-circle capture halfwidth is
β=acos((R²+ℓ²−U²)/(2Rℓ))
when|R−U|<ℓ<R+U, and zero forℓ≥R+U. The all-circle branchℓ+R≤U is impossible becauseR>U. The branchℓ≤R−U also has no intersection; for proposed smallδ one can enforce global ℓ≥(1−U)−(3U−1+δ)=2−4U−δ>δ, eliminating it. This formula reduces to acos(ℓ/(2U)) atδ=0.

Thus the same K1 nonnegative-measure dual applies with changedR/e-domain and denominator10 rather than11. This has now been certified for δ=1/20 over all12 closed e-segments: `evidence/nearmerge-interval-1-20.json` and `nearmerge-interval-1-20-tail.json`. C999 excludes all d≤1/10 at radiusU. The source/inference/record audit is `members/finite-reduction/onehub-audit/REPORT.md`; this is not described as an independent full nearmerge replay. Reproduction: `py -3 -B research-2026/n12-global/lead/nearmerge_interval_certificate.py 1/20` (or select tail segments `1/20 10,11`).
