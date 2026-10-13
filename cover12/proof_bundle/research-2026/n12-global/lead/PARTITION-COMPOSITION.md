# Exact composition of the pending-domain certificates

Scope: closed rational 3-box root H0 of the k10 hub chart; no assumption about realizability of all triples. Local predicates exclude legal covers only.

## Partition invariant
For a closed nondegenerate box B, split its first longest coordinate at its exact rational midpoint. Both closed children are subsets of B and their union is B; their interiors are disjoint. Recursively replacing any frontier box by these two children preserves the union, regardless of overlaps on boundary faces. A finite frontier is accepted only if recursive traversal from its declared root terminates at exactly the listed boxes, each encountered once, with no unused or duplicate box. This proves coverage; equal volume without containment and disjointness is not used as a replacement.

The fixed stage11825 frontier consists of 5909 terminal boxes and eight pending boxes. Independent verifier of the snapshot remains responsible for verifying its full root partition. Parallel planning replaces pending0 by four grandchildren (three binary splits), retains pending1..7 as single roots, hence has eleven roots. The same canonical rule makes each root an actual descendant of its corresponding old pending node.

For each root Bj, let Lj be its terminal leaves and Pj its pending leaves. A successful branch partition verification proves Bj=union(Lj union Pj). Substitution in the old full-root identity proves

H0 = union(old terminal leaves) union union_j Lj union union_j Pj.

Thus the original global gap has disappeared precisely when every Pj is empty AND all terminal predicates have been validated. A producer's status field or empty branch queue alone is not either of these statements. No mathematical claim is drawn from the number of accepted leaves or their total volume.

## Leaf predicates and quantifiers
An infeasible leaf L has an exact necessary-core/inactivity violation uniform over L, so no legal hub triple in L exists. An atomic leaf has fixed nonnegative integer weights, exact rational unit vectors, and an upper capture M valid for every hub triple in L and every normalized ring center, with 10M<T. For any putative legal covering whose hub triple lies in L, its ten rings must cover every retained atom; summing weights gives T<=10M, a contradiction. The certificate can exclude a box containing illegal triples without imposing witness necessity on those illegal triples.

## Computation and provenance
A merged payload must use exactly the bytes that passed the partition verification. Every root hash is bound to the fixed source snapshot and immutable plan. Producer hashes are provenance only; mathematical acceptance comes from reconstructing exact predicates/partitions. Integer-kernel replay reconstructs atoms from H/weights and the explicit per-N vector source. Cached results require equality of all these inputs and certified source provenance; matching row indices or a self-consistent key alone is insufficient. Final checker reruns the full root traversal on the merged file, so a correct local merge does not exempt the complete object from validation.

The same substitution may be iterated. The frozen `members/structure/parallel-domain/reshard-base.json` is the complete original-root partition with four pending boxes after merging the eleven original branches. Its independent prefix-tree proof is `evidence/reshard-base-prefix-partition.json`. The immutable `reshard-plan.json` replaces the first of those four by four grandchildren and retains the other three, producing seven roots. Generic workers `lead/run_planned_branch.py` bind that new base and plan, not stage11825 directly. Their eventual merged file is again checked from the original mathematical root; no recursive reliance on producer status strings is needed.

A forced stop loses only work since the last atomic checkpoint: restarting from that checkpoint retains all its pending boxes, so no branch is silently omitted. A partial checkpoint is still only partial, including when producer text inherited from a root-level driver says 'full domain' for one branch.
