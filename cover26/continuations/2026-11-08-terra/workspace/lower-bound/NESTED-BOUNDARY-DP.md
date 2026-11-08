# Finite optimization of nested boundary and core bounds

For n≥1 let L_n be any lower bound on the disk covering radius, and set L_0 as a special sentinel. For any integer 3≤b≤n, define

    A_b = sin(π/(b−1)),
    C_{n,b} = 1/2                            if b=n,
              L_{n−b}/(1+2 L_{n−b})           if b<n.

Then min(A_b,C_{n,b}) is an unconditional lower bound for r_D(n). Indeed, if r<both, the circle requires at least b *actual boundary-intersecting* disks, because b−1 of their arcs have total length less than 2π. Every boundary-intersecting disk misses the open disk of radius 1−2r, so at most n−b remaining disks cover its closure. If b<n, scale that core and contradict L_{n−b}; if b=n, no disk covers the origin. The argument does not require a minimal cover, projection, perturbation, or Voronoi topology. Smaller numbers of disks are padded by repetitions. It also handles disks tangent to the circle and coincident centers.

Starting with the area bounds L_n=1/√n, the exhaustive finite nested-boundary optimization is

    L_n = max(1/√n, max_{3≤b≤n} min(A_b,C_{n,b})),

computed in increasing n. This formula defines the strongest result of this particular recursive scheme; it does not bound the potential of other geometric arguments. One can substitute any independently proved better L_m as a seed and rerun, taking care never to promote a conditional or local bound into an unconditional seed.

For n=26, exhaustive interval arithmetic in `nested_dp.py` proves that the unique maximizing b is 16 and that the unique maximizing b at n=10 is 10. Thus the exact optimum **within this scheme** is

    sin(π/9)/(1+2sin(π/9)) ≈ 0.20309498890063.

It gives no improvement over the previously stated nested-boundary lemma. The closest alternate b=15 gives 1/5; b=17 gives sin(π/16)≈0.19509. Therefore progress beyond 0.203095 needs a stronger lower bound for a smaller-order problem, additional geometry that restricts the boundary disks or their inward reach, or the existing n26 global proof machinery; finer optimization of these same nested circle/core steps will not suffice.

The implementation uses exact Fraction arithmetic. Lower and upper rational sine enclosures use 333/106<π<355/113 and alternating Taylor polynomials; area seeds are enclosed using integer square roots. It prints each b and its two limiting thresholds, checks that every b other than 16 has upper bound below the b=16 lower bound, and checks the analogous unique choice at n=10. Floating displays are informational; assertions are rational. Run:

    python lower-bound/nested_dp.py

The statement distinguishes the actual boundary-intersecting disk count from the number of cells owning a unit-circle arc. A disk can touch the circle yet own none of it. No Voronoi-connectedness or dual graph assertion is used in this optimization. The older report's necessary-family section was rewritten to use actual disk counts and identifies the topology-to-dual interface as a separate unproved obligation.
