# Next sharp-angle acceptance obligations (discovery only)

Authoritative accepted state after the seventh stage is recorded in outputs:
215 FORCE, 13 LOCAL, 68 OPEN candidate angle leaves; 2,448 global combination
subtrees. n=26 global optimality is not proved and n=27 has not started.

Prepared, not accepted:

- `n26-sharp-root-angle-discovery-v1.json`: outward angle caps at scale 10^40,
  derived from the certified R* upper endpoint. The exact candidate survives
  all sharp difference constraints on 15 tiny rational angle cells. Of the
  68 accepted OPEN boxes, 3 become infeasible after sharp tightening.
  No whole global pending subtree was found infeasible by these constraints.
- `n26-sharp-cap-angle-continuation-proposal-v1.json`: source-bound discovery
  tree with 424 SPLIT, 215 old FORCE, 13 old LOCAL, 31 proposed SHARP_FORCE,
  166 OPEN. The three initially infeasible source leaves were not visited by
  the discovery budget; do not infer their absence from its zero SHARP_EMPTY
  count. Recheck every remaining OPEN during final acceptance.

Required before counting any of these discoveries:

1. Independently reconstruct four outward caps from the bound root endpoint
   and frozen exact trigonometry; certify every strict sine margin.
2. Reconstruct the necessary sharp difference matrix from rod paths.
   Write/review the short-chord and forced-arc interface explicitly. Do not
   impose D2 symmetry or assume any center is near the candidate.
3. Keep the accepted original U-domain tree and all old non-OPEN nodes intact.
   Evaluate sharper constraints at leaves: SHARP_EMPTY means infeasible for
   radius <=R*, not an empty original U-domain box. SHARP_FORCE must be
   rechecked on the fully reconstructed sharp box; SHARP_LOCAL must place the
   entire sharp box in the accepted nonlocal pinning domain.
4. Preserve both closed children of every new split, all shared boundaries,
   unreachable-node rejection, and every unresolved OPEN. Reclassify any
   remaining OPEN found sharp-empty/local without trusting discovery labels.
5. Publish a fresh immutable bundle, standalone standard-library replay,
   rejection controls, and a new current full-chain content audit. Only then
   update authoritative counts.

Possible later improvement, not proved/published: the generic rotation
allowance delta/8 is conservative. For delta<=10^-3, epsilon=delta/3,
a>0.9 and root center norms<1 suggest a simple exact estimate
|theta|<(9/8)epsilon and rotation movement<(23/20)epsilon; total coordinate
error<(43/60)delta, leaving room for the certified root-reference error.
This needs a separate verifier/proof bundle before replacing the accepted
7/800000 local allowance. Do not silently change the existing certificate.
