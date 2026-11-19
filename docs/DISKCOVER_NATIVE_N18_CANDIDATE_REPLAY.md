<!-- SPDX-License-Identifier: MIT -->
# n=18: all anchor angles of the candidate topology

**Completed scope.** The [native census](DISKCOVER_NATIVE_N18_CENSUS.md)
includes the exact upper candidate's twelve-owner topology. A new verifier
independently checks that **no strictly smaller cover can have that topology**,
over its whole anchor angle domain. This is one of the 14,559 native census
orbits, not the global result. The verifier uses the source tree's numerical
witness data, and does not run upstream scripts or accept a stored verdict.

## Normalization and graph identity

Take the radius \(\rho\) strictly between a hypothetical covering radius
\(r<r_*\) and \(r_*\) *before* applying the Voronoi geometric reduction.
Here \(r_*\) is the exact feasible algebraic radius isolated in the
[attainment replay](DISKCOVER_NATIVE_N18.md). Rotate or reflect a realization
of the candidate orbit and relabel the anchors, centers and face witnesses
into the **original** upper construction labels. Rotate about the disk center
so that the original candidate's \(q_0=(1,0)\). After a reflection, angles
are taken in the original forward order. None of these isometries changes
any rod length. The verifier compares canonical candidate face code and
stabilizer with the native census, binds the original face list to the
algebraic candidate, and checks the ninety original rod endpoints against
the native graph after transforming the interior face-witness indices.
The local isolation comparison never identifies an original anchor
\(q_0\) with a different fixed canonical anchor. It compares angles in the
original gauge only.

## Covering the full angle domain and accepting leaves

Normalize turns to \(u_0=0\) and start with \([0,1]^{11}\).
Tighten each box by exact short-arc difference constraints derived from the
verified angle caps and center adjacency. Every split is strictly inside
the tightened interval and its two closed children cover that interval.
The checker requires an in-range unique node index for each visit and
rejects unreachable nodes or any unsupported leaf kind.

At a force leaf, use a rational supporting halfplane that contains the arc
for each anchor. The proposed flow has integer numerators at denominator
\(10^{36}\); the nonnegative support multipliers have denominator \(10^{15}\)
and are rescaled exactly. The checker recomputes both the halfplanes and
the divergence, requiring every nonanchor force to vanish. It derives a
conservative residual support error directly from that certified data,
without trusting the supplied support offset. With \(d_i=\lambda_i a_i-F_i\),
discrete summation by parts and Cauchy--Schwarz yield the necessary
inequality
\[
 \sum_i\{\lambda_i(b_i-a_{ix})+d_{ix}-|d_i|\}
 \le \rho \sum_e |f_e|.
\]
The verifier uses outward integer-square-root norm bounds and proves
the left side strictly exceeds \(r_U\sum_e|f_e|\), for a rational
isolation endpoint \(r_U>r_*\). This excludes all \(\rho<r_*\) in the
box; it does not use a cover at radius \(r_U\) as the hypothesis.

At a local leaf, use exact directed rational bounds on the midpoint and
endpoint dot products of a free anchor's current arc and its candidate
anchor. If the arc span is less than half a turn and its midpoint dot
product is positive, the antipodal minimum cannot lie within that arc.
The minimum is therefore attained at an endpoint. Since both vectors
are on the unit circle, squared chord displacement is twice one minus
that dot product. The summed upper bound is checked against
\((7/60)^2\). The [exact matrix certificate](DISKCOVER_NATIVE_N18_ANCHOR_ISOLATION.md)
then rules out a strictly smaller realization of the 72 active rods,
which are a subgraph of the ninety-rod full graph. This test has no
restriction on center or witness displacement.

## Fresh replay

Save the [pinned candidate-tree witness data](https://github.com/VonEquinox/DiskCoveringSolve/blob/089584973f41e6374ce110f6e5b5ee456df19352/cover18/proof_bundle/core/candidate18_tree.json.gz)
with SHA-256
b0b5add76b82c2682e8447d7721860524fcaafe158de1181fc71ffa1472a3c2b.
Generate the native census's dfs-12.json by the linked command and save
the pinned root input documented with attainment. Then run:

    python -B verification/n18/candidate_data_replay.py \
      path/to/root18.json path/to/dfs-12.json path/to/candidate18_tree.json.gz \
      --negative-controls

The replay is standard-library-only. It accepts 609 splits, 548 rational
force exclusions, and 62 local boxes, all 1,219 nodes. Every
force margin exceeds \(1/50000000\), and every checked local box has
squared anchor displacement below \(17/1250 < (7/60)^2\).
Negative controls exercise cyclic child, oversized local box and
zero-force rejection. See [the fresh receipt](../verification/n18/candidate_replay_receipt.json).
An exploratory one-CPU LP-only regeneration at depth 18 found open leaves;
the final complete replay uses the pinned witness splittings and
integer flows instead.

**Unpaid:** continuous force or other global exclusions for the
remaining 14,558 canonically distinct screened orbits.
