# Unrestricted n=12 global optimality theorem

**Status: proved, computer-assisted global theorem.** The remaining k10 implication is established in `K10-FULL-EXCLUSION.md` (C1139): exact original-root partition, all318 prune predicates, all6723 atomic certificates with content-bound fresh provenance, zero pending. Final source bytes were independently joined by `final_content_audit.py`; the integer kernel has independent mathematical/representation audit. This is not formal proof-assistant verification or external peer review.

Let D be the closed unit disk and r_D(12)=inf_C max_{p∈D} min_{c∈C}|p−c|, allowing twelve arbitrary centers in R², repeated centers, and closed disks.

## Exact answer
Let (a,t,r,w) be the unique solution in the rational box in `evidence/root-t-certificate.json` of F=G=H=T=0, where

b=(1+a+r)/2, S=b²+w²/3, A=3b²−w²−2bw,
F=a²+ar−at−2rt+t²,
G=(1+t²−r²)(3b²+w²)−t(3b²−w²+6bw),
H=4w²−12r²+3(1−a−r)²,
T=w S²(2a−t+r)(1−t²−r²)+(S−b)(2t−2r−a)t²A.

The rational box has center (the following decimals are EXACT rationals)
(a,t,r,w)=(.27824166087442791214863102289847881,
.76916901916340509329976934431759555,
.36110296374450864411308770201706518,
.54187805494572479061805294826929084)
and halfwidth 10^-30 in every coordinate. These exact rational midpoints and halfwidths were independently extracted from the authoritative JSON endpoints; they define the same isolating box.

Write r*=r. Root existence and uniqueness are established by an exact rational Banach contraction, and r*<U=22568935234031792038557518369/62500000000000000000000000000. Numerical display only: r*≈0.36110296374450864411308770201706518.

An attaining construction has three hubs a u(2πj/3), three lows t u(π/3+2πj/3), and six highs obtained by rotating (b,±w/√3) by 2πj/3, j=0,1,2. Here u(θ)=(cosθ,sinθ). The exact ideal-coverage proof (C985) establishes coverage of the entire closed disk, including polygon exterior strips, not just its boundary or a finite numerical mesh.

## Complete logical split
1. Project all centers to D; this does not increase any target-point distance. Compactness gives existence of an abstract minimizing configuration (C925). These steps do not impose symmetry.
2. Suppose a covering radius r<r*. Then r<U. Boundary-active includes tangent disks. By C926 the actual active count is k∈{9,10,11}.
3. For k=9, C986 gives r≥r* by a full cover-to-network reduction, classification into56 networks,55 strict exclusions, and the sharp333 stress proof on the entire anchor simplex. Contradiction at the ORIGINAL radius; no active-count assumption after enlargement is needed here.
4. For k=10 or11, enlarge every disk to radiusU. Active count can only increase, and C926 atU bounds it by11. Thus the enlarged count is10 or11. C998 excludes11.
5. For exact10 atU, inner-root replacement normalizes the ten active centers into the full annulus [1−U,sqrt(1−U²)], preserving coverage and active labels. The remaining two centers are strictly inside radius1−U. They must cover the closed core of radius a0=1−2U.
6. If their distance d≤1/10, C999 excludes them via the midpoint-circle dual. If d≥2U, the elementary core/inactivity lemma `STRICT-HUB-SEPARATION-LEMMA.md` excludes them: all legal pairs have d<2U. This branch no longer needs a capacity-certificate premise.
7. Otherwise rotate, reflect, and exchange hub labels to write h1=(x−s,y),h2=(x+s,y), s=d/2∈[1/20,U], x,y≥0. Necessary core/inactivity inequalities give x≤1−U−1/20 and y≤3U−1. This is exactly the root box of `hubline_domain.py`. The independent interface audit proves all three domain-deletion tests are safe and every retained moving atom must be covered by the ten rings. C1139 establishes that every box in this entire root domain is either certified infeasible or excluded by a certified atomic dual, with no pending boxes. See `K10-FULL-EXCLUSION.md` for the analytic proof, full manifest, exact replay, hashes and independent interface audits.
8. Step7 contradicts the last possible branch. Therefore all smaller-radius covers are impossible. Combining with the explicit C985 construction proves **r_D(12)=r***. All quantifiers are over arbitrary twelve centers in R², not a prescribed family.

## What is NOT required
No uniqueness of the optimal configuration, exact D3 symmetry of arbitrary covers, prescribed9+3 structure, general position, or irredundancy is assumed. The proof need not show an optimizer has k9 until k10/11 are excluded. Numerical LP proposals are arbitrary witness generators; their feasibility and numerical optimality are not bearing premises in the atomic exclusion.

## Evidence and reproduction

- Root and attaining cover: `root_t_certificate.py`, `ideal_coverage_certificate.py`; C985 and the coverage audit.
- Entire k9 lower bound: `K9-SHARP-THEOREM.md`, `replay_network_certificates.py`; C986.
- k11 and nearmerge: C998/C999, their analytic notes and interval evidence/audits.
- Full k10: `K10-FULL-EXCLUSION.md`; immutable manifest SHA256 `7f44132b8dd09c8377b7e300caebe6ca5485b8933bde86455f67062733c1c57a`.
- Final whole-content check: `py -3 -B research-2026/n12-global/lead/final_content_audit.py`. Full integer replay commands are in `members/finite-reduction/integer-domain/REPORT-STRICT-VERIFICATION.md`.

## Comparison with the original success criteria

C182/C191 were inspected and finitely reproduced at the outset; C934 replaces the unsupported historical-source wording, C191 remains numeric. The exact answer above is a uniquely isolated algebraic root, not a finite decimal. C985 attains it and steps1–8 exclude every smaller radius. No9+3/D3/contact-graph/general-position hypothesis is used for arbitrary covers. n11 assets were read-only and no n11 result is needed as a sharp numerical premise. All new proof products lie in `research-2026/n12-global/`. **No remaining mathematical gap in this assembled proof is identified.** Novelty, external peer review, and uniqueness of optimizers are not claimed.
