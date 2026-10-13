# Current candidate continuation

This extension starts with the semantically replayed accepted continued-leaf-v1
tree, not the older leaf-pinned tree and not discovery summary counts.
The historical loader first reconstructs all original pinning and force
payments; the continued-source loader reconstructs the actual accepted
continued tree, its exact ledger and all remaining closed OPEN boxes.

Every previously non-OPEN node, including every closed split, stays identical.
Only an old OPEN leaf can be replaced. The full new tree is replayed with the
same exact arithmetic and the same radius-conditional necessary constraints.
Each split retains both closed halves and every node must be reachable once.
Every new force lower bound must strictly exceed the certified same-root
radius upper endpoint. Numerical solver objectives and discovery counts are
never acceptance evidence.

Hull-local leaves are rebuilt from the whole sharp leaf and exact candidate
tiny box. Their energy/Dirichlet pinning is independently recomputed and must
enter the unchanged original-coordinate local allowance 7/800000.
The known exact candidate tiny box must remain in an accepted LOCAL leaf.
All unresolved leaves are explicitly published, even if splitting increases
their number.

These are radius-at-most-Rstar conditional exclusions, not unconditional
exclusions at the larger screening threshold U. No combinatorial frontier is
removed by this continuation. Global optimality, complete enumeration and the
final unrestricted reduction are not claimed.
