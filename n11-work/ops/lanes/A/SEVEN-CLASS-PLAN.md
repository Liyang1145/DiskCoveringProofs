# SevenClassExclusions implementation plan

Status: 2026-10-28 scoping only.  No new Lean theorem or kernel claim is made
by this file.  The seven fields are explicit unpaid premises in
`ActualMetricClassReduction.SevenClassExclusions`.

## Exact target interface

`ActualMetricClassReduction.SevenClassExclusions` has seven fields:

| Lean field | definition | run length | hub degrees |
|---|---|---:|---:|
| `q0_degree3` | `Q0RunExclusion 1` | 1 | (3,10) |
| `q0_degree4` | `Q0RunExclusion 2` | 2 | (4,9) |
| `q0_degree5` | `Q0RunExclusion 3` | 3 | (5,8) |
| `q1_degree3` | `Q1RunExclusion 1` | 1 | (3,9) |
| `q1_degree4` | `Q1RunExclusion 2` | 2 | (4,8) |
| `q1_degree5` | `Q1RunExclusion 3` | 3 | (5,7) |
| `q1_balanced` | `Q1RunExclusion 4` | 4 | (6,6) |

The degree conversion is the proved formula in `ActualQ0RunDegrees` and
`ActualQ1RunDegrees`; it is not a new classification premise.  The seven
fields exclude all q1 run lengths produced by the exhaustive finite-family
producer, but only q0 lengths 1--3.  In particular `q0(6,7)` is **not** an
exclusion field: `actual_metric_classification_of_seven` handles q0 run
length 4 through the proved canonical-nearest rows.  The source q0 closure
certificate for `(6,7)` is scoped only to `r <= 3/8`, so it cannot be inserted
here, where the target is `r < 19/50`.

Consumer chain:

- `ActualFiniteFanFamilies.actual_exhaustive_ordered_families` reduces every
  representative to one of the seven run lengths above.
- `CanonicalSharedMomentFiniteCertificate.q0_exclusion_of_table` and
  `q1_exclusion_of_tables` turn finite tables into the corresponding run
  exclusions.
- `CanonicalBalancedFiniteClassCertificate.balanced_exclusion_of_two_finite`
  turns two balanced representative tables into `Q1RunExclusion 4`.
- `seven_classes_of_six_and_two` assembles `SevenClassExclusions` from six
  direct tables and the balanced pair.

## Source evidence and table count

One `CanonicalCertificate` has 11 face factors, 9 switch factors, and 9
sector factors: 29 rational factor bounds, matching the 29 factor records in
the source certificate JSON for the q0 and q1 factor-style certificates.

| Lean field | source argument | committed evidence | source cases | direct Lean certificates |
|---|---|---|---:|---:|
| `q0_degree3` | C812 degree-three exclusion, q0 graph | `degree3_fraction_control.json` row with `q=0`; `DEGREE3-AREA-EXCLUSION.md` | 1 | 1 |
| `q0_degree4` | C819 q0(4,9) moment dual | `q0_moment_dual_certificate_0_2.json`; `Q0-DEGREE4-EXCLUSION.md` | 1 | 1 |
| `q0_degree5` | k3 q0(5,8) closure dual | `q0_closure_dual_certificate_0_3.json`; `Q0-CLOSURE-EXCLUSIONS.md` | 1 | 1 |
| `q1_degree3` | C812 degree-three exclusion, eight q1 positions | eight `q=1` rows in `degree3_fraction_control.json` | 8 | 8 |
| `q1_degree4` | C813 degree-four q1 exclusion | four rows in `degree4_triple_fraction_control.json`; `DEGREE4-TRIPLE-EXCLUSION.md` | 4 | 4 with orbit transport, otherwise 8 |
| `q1_degree5` | C817, plus start 7 by C815 | four `shared_factor_certificate_{0..3}_3.json` and `compatible_position_certificate.json` | 5 | 5 with orbit transport, otherwise 8 |
| `q1_balanced` | C818 balanced q1 exclusion | `shared_moment_dense_certificate_{0,2}_4.json` | 2 | 2 |

Direct-table total is therefore 29 `FiniteCanonicalCertificate`s, hence
`29 * 29 = 841` factor-bound values.  Existing balanced orbit transport
already covers all eight balanced cuts from the two tables.  To reach the
22-certificate count for q1 degree 4/5, new finite graph-orbit transport is
needed; direct emission of all eight cuts avoids that extra transport layer.

Known serialized coefficient counts in the committed factor-style files:
q0(4,9) 112, q0(5,8) 121, each q1(5,7) shared table 73 (four tables),
q1(5,7) compatible position 24, and each balanced table 112 (two tables).
That is 773 serialized coefficients across those nine source certificates.
The degree-3 and degree-4 files retain exact rational upper controls but not a
complete `CanonicalCoeffQ` layout.

## What already exists in Lean

- Exact rational coefficient transport and pullback:
  `ActualCanonicalMomentTransport` (`CanonicalCoeffQ`, mask balance and factor
  pullback).
- Actual-coordinate and fan matching:
  `ActualCanonicalSharedMomentConsumer` (`q0Coordinates`, `q1Coordinates`,
  `exclude_q0_ordered`, `exclude_q1_ordered`).
- Finite certificate format and semantic consumer:
  `CanonicalSharedMomentFiniteCertificate.FiniteCanonicalCertificate` and
  `CanonicalSharedMomentFiniteCertificate.Q0FiniteTable/Q1FiniteTables`.
- Balanced reduction and finite graph automorphisms:
  `CanonicalBalancedFiniteClassCertificate.BalancedTwoFiniteTables`,
  `CanonicalBalancedGraphOrbits`, and `CanonicalSharedMomentOrbitTransport`.
- Run-length/degree correctness:
  `ActualQ0RunDegrees.actual_q0_run_degrees` and
  `ActualQ1RunDegrees.actual_q1_run_degrees`.

These modules prove the consumer and transport steps.  They do not contain
any of the 29 required finite tables.

## The real gap: source JSON is not a Lean certificate

The JSON records floating interval endpoints, factor names, evaluation counts,
and coefficient vectors.  `FiniteCanonicalCertificate` additionally requires
proof terms of type `EfficientFaceCertificate`, `SwitchCertificate`, and
`EfficientSectorCertificate`, plus `CanonicalMaskBalancedQ`, nonnegative edge
multipliers, and an exact rational `canonicalTotalUpperQ < RatInterval.piLo`.
Numeric JSON fields cannot inhabit those propositions.  The source scripts,
their interval kernels, and their graph reconstruction are the certificates;
the saved output alone is an index to them.

The required bridge is therefore:

1. Reconstruct each source graph independently from the committed emitter and
   match its labelled face set exactly to `q0Faces m` or `q1Faces k m`.
2. Extract the source coefficient vector into the named
   `CanonicalCoeffQ` fields.  Positional guessing from 73/112/121 coefficients
   is forbidden; the field order must be emitted from the reconstruction.
3. Replace floating factor records with proof-producing exact rational factor
   bounds that construct the three certificate structures.
4. Check mask balance and nonnegative multipliers as exact rational identities.
5. Check the final rational total against `RatInterval.piLo`, then emit the
   table and record CI status.  A successful source replay or byte audit is
   still not kernel acceptance.

The hardest step is item 3.  The existing Lean factor-grid certificates can
supply the proof shape, but the source subdivision and coefficient layout must
be replayed into Lean rather than accepted as cached verdicts.  Reusing the
source's `strict: true` flag or its decimal bound is not enough.

## Proposed implementation order

1. Pilot `q0_degree4`: one graph, one table, 112 source coefficients, 29 factor
   bounds, and no orbit transport.  Emit only an exact inventory manifest and
   graph-match report first.
2. Add a deterministic `extract_finite_class_tables.py` that writes rational
   coefficient records and refuses any graph or field-count mismatch.
3. Build the proof-producing factor bridge for the pilot, emit
   `Q0Degree4FiniteTable.lean`, add it to `TARGETS.txt`, and wait for CI.
4. Reuse the bridge for `q0_degree5` and the eight `q1_degree3` tables.
5. Emit q1 degree 4/5 either as eight direct cuts or as source
   representatives plus a new orbit-transport module.  Prefer direct cuts
   until the orbit module is proved.
6. Instantiate the two balanced tables through the existing orbit transport.
7. Build `SevenFiniteTables` only after all 29 certificates are CI green.
8. Request root integration of the seven-class consumer only after the
   supporting modules and the separate energy/C450 obligations are checked.

## Bounds recorded by the source audit

- q0(4,9): `[2.97871288362012352436665185421, 2.9787128836201235243666522678] < pi`.
- q0(5,8): `[3.09579300912180273035495257169, 3.09579300912180273035495443285] < pi`.
- q1(5,7): five saved upper endpoints, largest `3.139627044416903102133305523983083042719 < pi`.
- q1(6,6): two saved upper endpoints, largest `3.13981254422259203355720550464 < pi`.
- Degree-3 exact rational controls pass for one q0 and eight q1 cases, all
  below `314159/100000`.
- Degree-4 exact rational controls pass for four q1 representatives, all
  below `314159/100000`.

All these are source-level statements, not Lean elaborations.  The source
ledger explicitly notes that the q1 closure kernels have one interval
implementation, not two independent arithmetic kernels, and that numerical
identity checks are calibration only.  Those qualifications must survive the
Lean port.

## Unpaid obligations after this plan

- All 29 finite tables above remain unconstructed in Lean.
- Source-to-Lean graph/coefficient correspondence remains unaudited.
- The q0(6,7) canonical-nearest non-exclusion and its source-scope caveat
  remain untouched.
- Energy `RemainingTerminalRadius` and the C450 telescope remain separate
  obligations.
- The A25 framework acceptance is not the arbitrary-center full-disk theorem.

## Session checks and hashes

`python3 n11-work/ops/lanes/A/audit_seven_class_inventory.py` was run on this
tree.  It checks file presence, exact rational bound ordering, expected source
case counts, factor/coefficient record counts, and presence of the seven Lean
fields.  Result: PASS for source inventory only; no Lean/kernel claim.

Key SHA256 values:

- `ActualMetricClassReduction.lean`: `4c6b872adbd37a812898a80c39decf1cb500937a6e79a695d06f6fc3320c8936`
- `CanonicalSharedMomentFiniteCertificate.lean`: `f3a05b26fdef1b67a91e2fd48f4b580d81ea99dfc11e1fdc48234cf760434cfd`
- `CanonicalBalancedFiniteClassCertificate.lean`: `f71d338797184f8550c407fbd0e9cfd53cc4246f42581608750ecf7ea968644a`
- `CanonicalBalancedGraphOrbits.lean`: `bbb7f9466029a665379f666851626f37d60c602eac89439a03b943d705d128ad`
- `CanonicalSharedMomentOrbitTransport.lean`: `17f49b41c2c3898708a9a210c976e65d39b79c482fcfead11d9a632fbaca035c`
- `DEGREE3-AREA-EXCLUSION.md`: `ea57ef6f2b71518d36d47518ba3c88aab1d66dbf1ca9576079fbbfb2f7fc569e`
- `DEGREE4-TRIPLE-EXCLUSION.md`: `e241b272502503fc514402254cb5e6202ebe4f52727f3fa44ed20478989c85a4`
- `Q0-DEGREE4-EXCLUSION.md`: `b2234e651c5edff3b64af5e37b30f9db49b5509e108a13b3337b32ace59276bc`
- `Q1-DEGREE5-EXCLUSION.md`: `150a59a9d74b8d44c89943fc3ea330897939970809a0b19ea293e5874cdbaf84`
- `Q1-BALANCED-EXCLUSION.md`: `534fef6de1317d4251ef152a3950618e723a8c363bd97ce0d0292cc0bbae774d`
- `Q0-CLOSURE-EXCLUSIONS.md`: `6fe7ee09df105ab10ba775faaab335423f40c46a382e35e92c08dcc0d5649e38`

Certificate/control SHA256 values:

- `degree3_fraction_control.json`: `83e071a75512c83cf87b96794ed4f1d7b6b3f5a90a5787603d2efdef3b7580c1`
- `degree4_triple_fraction_control.json`: `7a26fdcc61b3accf642c55d85d76d082e297f622b03b4c123f2a254360a0f8cb`
- `q0_moment_dual_certificate_0_2.json`: `5759e36f602ea5837f87dd7d20edd3be48ebdf67e19d062c7077501659ccedea`
- `q0_closure_dual_certificate_0_3.json`: `d765b2abcf957edf3f33d16659f456b12015f6807d98653c2e4c70522c62d9ba`
- `shared_factor_certificate_0_3.json`: `3e7b329870d04fad7fb06c41f3be8b9c97352a04d6bc7e68a0ee8fd3dddbc2ff`
- `shared_factor_certificate_1_3.json`: `8126d9079fa707c953c0bdd5c6e7700a40a82c0ccb6612998eb27a56b57ac484`
- `shared_factor_certificate_2_3.json`: `61cb31e6c18fa13a8784411f7edbb40ba2d0fde14c0579da047d81eb5d5c0971`
- `shared_factor_certificate_3_3.json`: `5c759f15ffa024fa470196bc472e943ada3319d343e539ca6b63927134eca28b`
- `compatible_position_certificate.json`: `c926931ac805ce7fb6cb43ac19b758121d8277858b2d74e09c1db9aab55622e2`
- `shared_moment_dense_certificate_0_4.json`: `c00e0924696a90709f62b72e97cbe3fb01f90a8ef613ca61b97b32876ec667de`
- `shared_moment_dense_certificate_2_4.json`: `5cea2f22a342a2226c92c28a5fa5498f9eacbf683a95440575bc952d0dac038f`

## Immediate next step

Implement the graph-match half of `extract_finite_class_tables.py` for the
q0(4,9) pilot.  It should reconstruct `q0Faces 2` and the source graph from
`check_q0_moment_symbolic.py`, compare labelled face/edge sets and coefficient
field counts, and emit a manifest with no Lean claim.  Do not emit the Lean
table until that match is exact.

## q0_degree3 exact statement and Lean reduction (2026-10-28)

Field:
`Q0RunExclusion 1`, i.e. for every representative `(c,r)` with
`r < 19/50`, every refinement `R`, and every ordered q0 data `O` with
`O.run_length.val = 1`, `False`.

Math route from `DEGREE3-AREA-EXCLUSION.md`:
1. A q0 run of length one has hub degrees 3 and 10. The actual graph is
   already normalized by `ActualOrderedMetricGraphs.actual_q0_degree_three_table_graph`
   to the unique unrotated 21-edge table (up to the produced label rotation).
2. For that table, the source certifies rational multipliers `mu`, `lambda` and
   grid/Lipschitz maxima over the whole angle domain with interval arithmetic.
   The dual upper bound is `< pi`, contradicting the actual area budget; the
   Lean emitter must still turn the maxima into exact rational data.
3. The generic Lean consumer
   `MetricAreaRationalCertificate.exclude_representative_of_rational_certificate`
   checks all node inequalities and the final strict rational inequality.

New module `N11Formalization/SevenClassQ0Deg3.lean`:
- `Degree3AreaCertificate h hr R` bundles exactly the consumer data for one
  actual refinement (including `NineTies`, node vector, edge/sector maxima,
  and the strict bound).
- `false_of_areaCertificate` feeds that bundle to the existing consumer.
- `Q0Degree3AreaInput` is the exact remaining universal obligation: supply
  one such bundle for every actual q0 length-one run.
- `q0_degree3_of_areaInput : Q0Degree3AreaInput -> Q0RunExclusion 1`.
- `degree_three_table_graph` restates the unconditional unique-graph result.

This is a reduction, **not** a proof of the field: `Q0Degree3AreaInput` is
not inhabited. In particular, the node maxima still must be emitted from the
source certificate into exact rational Lean data and kernel-checked by CI.
