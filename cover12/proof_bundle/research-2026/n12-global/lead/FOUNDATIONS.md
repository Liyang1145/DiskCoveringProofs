# n12 unrestricted foundations and next implication

Object: D={x in R²: ||x||≤1}; twelve labelled centers in R², repetitions permitted; R(C)=max_{x in D} min_i||x-c_i||. U=0.361102963744508672616920293904 is an exact rational, not a root definition or optimality assertion.

## 1. Compact attainment (analytic, global, independent of candidate)

Let P(c)=c for ||c||≤1 and c/||c|| otherwise. For c=tu, t>1, and x∈D,
||x-tu||²-||x-u||²=(t-1)(t+1-2 x·u)≥(t-1)²≥0.
Thus projecting every center into D cannot increase R(C). For C,C'∈D^12,
|R(C)-R(C')|≤max_i||c_i-c'_i||: pointwise each distance changes by at most that amount, and taking min then max preserves the inequality. Hence R is continuous on compact D^12 and has a minimizer. This proves the infimum is attained, but does NOT identify the minimizing radius or configuration.

The covering definition is equivalent to R(C)≤r by compactness of D and continuity of the nearest-center distance. Lebesgue area gives 1≤12r² for every cover, hence r_D(12)≥1/sqrt(12)>0. Neither this nor abstract attainment constitutes the requested sharp theorem.

## 2. Boundary-active count (analytic, global below U)

Call a disk boundary-active when B(c,r)∩∂D is nonempty (even a singleton). Assume r≤U<1/2. If c=0 it is not active. For c=tu, t>0, the covered directions satisfy cos θ≥(1+t²-r²)/(2t). A nonempty intersection is a closed arc of half-angle α in [0,π/2); the AM-GM identity
(1+t²-r²)/(2t)=(t+(1-r²)/t)/2≥sqrt(1-r²)
gives α≤asin r. Full boundary coverage therefore entails k asin r≥π for k active disks, even with overlap or degenerate arcs.

For k≤8, r≥sin(π/8)=sqrt(2-sqrt(2))/2>3/8>U. The strict radical bound follows from sqrt(2)<23/16, whence (2-sqrt(2))/4>9/64. So k≥9.

Some disk contains the origin, so its center obeys ||c||≤r. Every point of that disk has norm≤2r<1, making it nonactive. Therefore k≤11. This is valid before or after projection and without irredundancy or general position assumptions. The remaining count classes are k=9,10,11; no class has yet been eliminated.

## 3. Audit of the replay kernel

D1 recursively partitions [-1,1]² into four closed boxes. It discards only boxes whose exact minimal squared norm exceeds one, or boxes B for which an upper bound on max_{x∈B}||x-ci|| for some center is ≤U. The latter is sufficient for all B∩D to be covered. Its nearest_fixed branch uses exact affine inequalities to find a nearest center on the whole box; even if this optimization were omitted, any selected center's distance upper bound remains sufficient. The actual upper distance is the maximum of four corner squared distances followed by an outward rational sqrt. No distance lower bound is used for the coverage acceptance predicate.

In certlib, for q=p/d≥0, m=isqrt(p d 2^96) implies
(m/(d 2^48))²≤q<((m+1)/(d 2^48))².
This proves the sqrt enclosure by integer arithmetic. Terminal success means all finite leaves have been discarded soundly. A depth/box-limit failure is inconclusive.

The Python loader uses Fraction on each original centers_dec17 string and rounds on the 10^17 lattice. All original strings already lie exactly on that lattice; the replay verifies equality of all 24 coordinates, not just numerical closeness.

Replay: `py -3 -B research-2026/n12-global/lead/replay_initial.py` (180-second child timeout). Evidence: `../evidence/initial-replay/controls.json`, `c182-d1-d2-replay.txt`, `run.json`. D1 succeeds: 8057 boxes, 1421 outside leaves, 4622 covered leaves, maximum depth 101. Exact claim fraction 22568935234031792038557518369/62500000000000000000000000000 is U. Printed 28-place upper decimal is deliberately rounded outward; it is NOT the literal claim object. Positive one-center test r=3/2 passes; negative r=9/10 does not pass and has exact uncovered point (1,0). Sqrt squared-inequality controls include zero and large/small rational arguments. D2 has a known one-nonzero-center radius 5/4 control. D3 object identity and legacy diagnostic discrepancy are delegated separately.

## 4. Current structural obligation, not yet solved

Obtain a full finite representation of unrestricted covers, valid on all duplicate/collinear/tangent/zero-center strata; then exploit boundary count and interior coverage jointly. A representation alone is not sharp exclusion. The missing main implication is still: any covering configuration with r<U (or a rigorously isolated future candidate root) must satisfy r≥R*. No symmetry, 9+3, or candidate contact graph is assumed.
