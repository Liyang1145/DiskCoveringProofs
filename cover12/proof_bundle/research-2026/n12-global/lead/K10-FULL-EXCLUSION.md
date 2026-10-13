# Full k10 exclusion at the exact rational radius U

**Level:** computer-assisted proof, global over all radius-U covers with exactly ten disks meeting the unit circle. Closed disks, arbitrary centers, repeated centers and tangencies are allowed. No symmetry assumption. This statement concerns the entire class, not the numerical proposal family.

Set U=22568935234031792038557518369/62500000000000000000000000000 and a0=1−2U.

## 1. Reduction from a cover to the root domain

Project centers into D before classifying activity, if needed. For the k10 statement here centers are in D and exactly ten disks meet S1. `INNER-ROOT-REDUCTION.md` proves **D∩B(old,U) ⊆ D∩B(new,U)**, not merely equality of boundary arcs. Replace each active center by the inner radial root. Coverage and exact activity labels survive. The ten active centers now satisfy 1−U≤|c|≤sqrt(1−U²); the other two centers satisfy |h|<1−U.

The ten active disks miss the open core |p|<a0. Thus the two closed hub disks cover its closure. C999 excludes hub separation d≤1/10. `STRICT-HUB-SEPARATION-LEMMA.md` (C1113) proves d<2U directly from core coverage and strict inactivity. Rotate, reflect and relabel the pair to write h1=(x−s,y), h2=(x+s,y), x,y≥0, s=d/2. These operations impose no symmetry on the cover. Inactivity gives x+s<1−U. Covering (0,−a0) gives (x−s)²+(y+a0)²≤U². Hence all remaining legal pairs belong to the closed rational box

    H0 = [1/20,U] × [0,1−U−1/20] × [0,3U−1].

The enlarged box contains nonlegal triples. Excluding such a superset is harmless; necessity of witness coverage is asserted only for legal triples.

## 2. The two kinds of terminal box

For H⊆H0, the three infeasibility predicates are justified in `ATOMIC-DUAL-PROOF.md` and independently in `members/structure/atomic-interface/AUDIT.md`:

1. A lower bound on |h2|² violates strict inactivity.
2. A fixed exact rational point of the core circle has distance greater than U to both hub rectangles.
3. If x_hi<a0, the core bisector endpoint requires s_lo²+(y_lo+sqrt(a0²−x_hi²))²≤U². Its violation is tested by sign-safe exact rational squaring; a separate isqrt enclosure crosschecks the radical expression.

Every other terminal box carries a finite atomic measure. Boundary atoms are exact rational unit vectors. Hub atoms are hj+Uv, retained only when Uv_x≤s_lo for hub1 and Uv_x≥−s_lo for hub2. Then each retained atom is outside or on the other hub for every triple in H. Hub circles lie in int(D). Perturbation outside both hubs, followed by closedness of the ten-ring union, proves that every retained atom must be covered by a ring. At an intersection atom the vector n1+n2 has positive scalar product with both outward normals because 0<s<U. The s=U face has no legal pair, by C1113.

Each atom has a nonnegative integer weight. Multiplicities cause no difficulty. Write T for total demand. For every ring-center rectangle the outward integer atom rectangles give an upper bound on captured weight. The annulus tests discard only rectangles containing no legal ring center. Exact dyadic subdivision of [−1,1]² exhausts the ring domain. If every surviving terminal ring rectangle has capture at most M with **10M<T**, ten rings cannot cover the atoms.

`ATOMIC-DUAL-PROOF.md` gives the analytic argument and arithmetic bounds. `members/stress-audit/atomic-final-audit/REPORT.md` independently derives the rectangle-distance direction, annulus rejection, exact weight construction, strict union bound and DFS coverage. At S=2^28 the conservative squared-distance bound is 32S²=2^61<2^63; weight sums stay below2^60, and factor10 comparisons use Python integers. N=2048 or8192 only chooses a finite measure, not a quadrature approximation. Numerical LP coefficients propose weights; no numerical LP optimality is used.

Screening is a bearing parameter. All fresh certificate calls use the frozen class's screened default. `members/finite-reduction/integer-domain/SOURCE-CALL-CONTRACT.md` records signatures and calls. `screen=False` would not support the geometric implication and is not an accepted mode.

## 3. Exhaustive finite certificate and binding

Immutable complete manifest:

- `members/structure/parallel-domain/completed-domain-base.json`
- SHA256 `7f44132b8dd09c8377b7e300caebe6ca5485b8933bde86455f67062733c1c57a`
- 6723 atomic leaves,318 infeasible leaves,**0 pending**;7040 internal binary nodes.

`lead/check_partition_trie.py` reconstructs a complete canonical binary prefix tree from the leaves, independently of producer helpers, and compares its root with H0 exactly. Its evidence is `evidence/completed-domain-prefix-partition.json`. Thus these leaves cover the **whole original domain**, including all shared faces.

The finite-reduction verifier rechecks all318 pruning predicates, crosschecking all187 third-predicate instances by radical enclosure. Every one of the6723 atomic leaves has a certified replay row with strictly positive exact gap; the minimum gap is6 integer weight units. N counts:6031 at2048 and692 at8192. Scales:6720 at2^26 and3 at2^28. Scale is stored and content-bound, never silently promoted. Earlier producer result fields and old box counts are diagnostic only.

The final run reused6449 content-identical earlier certified leaves and freshly replayed274 new leaves. Reuse is not assumed from a cache key alone: the provenance audit resolves every row to an actual saved fresh source row, its source snapshot leaf, vectors, kernels and scale. `lead/final_content_audit.py` performs a separate full6723 join of the actual current and source H/weights/N, source snapshot hashes, fresh file/line, numeric demand/capture/gap and all current kernel/vector hashes. This is independent content binding, not an independent second implementation of the whole integer replay.

Final frozen outputs (`members/finite-reduction/integer-domain/out/`):

| file | SHA256 |
|---|---|
| certified-cache.jsonl | 76a44a4e1988a6fa6ce237fb161a027cea75f78000ab478ee260732df96dd22e |
| cache-provenance.json | 0066dae3b7c2f656132bfa569fc820fa82317b09f5790d8355c28f44eab4904f |
| verify-completed-domain.jsonl | d1f2e6e9be25d03001d6a7f665854b798cfb470bb1ba6ac986a1ae49b3ee0ee7 |
| verify-completed-domain-summary.json | 244c3cce5f6e73b8a30a1d11b24dbca01453860c14008867c6d32b66605dccce |

The first final-byte audit rejected a stale provenance cache hash caused by binding after provenance and a control test appending a synthetic leaf. The production cache was rebuilt only from registered production ledgers, the synthetic record was quarantined, provenance regenerated after the last write, and the final independent join passed. Those rejected intermediate hashes are not premises here. The earlier bad wave4 merge is likewise not a premise.

## 4. Conclusion and reproduction

A legal cover in H0 must belong to at least one terminal box. An infeasible box contradicts a necessary geometric condition; an atomic box contradicts the required weighted cover. Thus no legal pair remains. Together with C999 and C1113 this excludes **all k10 radius-U covers**.

Quick content/partition verification (does not repeat all ring subdivisions):

    py -3 -B research-2026/n12-global/lead/final_content_audit.py
    py -3 -B research-2026/n12-global/lead/check_partition_trie.py research-2026/n12-global/members/structure/parallel-domain/completed-domain-base.json research-2026/n12-global/evidence/completed-domain-prefix-recheck.json

Full replay/provenance commands: `members/finite-reduction/integer-domain/REPORT-STRICT-VERIFICATION.md`. Kernel independent-inference/control commands: `members/stress-audit/atomic-final-audit/REPORT.md` §5.

No uniqueness of an optimal arrangement, no novelty priority, and no formal proof-assistant verification is asserted.
