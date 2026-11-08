# n=26 global lower bound 28/125 and exact radius-9/40 branches

The following new unconditional bound was verified by exact rational interval checks:

    r_D(26) > 28/125 = 0.224.

In addition, if 26 closed disks of radius 9/40 cover the unit disk, the number B of disks that actually meet the unit circle must be 15 or 16. This is a necessary condition, not an optimum claim, and B is not a Voronoi-owner count. The following proof applies to arbitrary, repeated and degenerate centers.

## Integer group inequality

Fix r<1/2, and assign each disk by its center norm d to one of three ranges:

    C: 0≤d≤r;    M: r<d<1−r;    O: d≥1−r.

At least one disk is in C because the origin must be covered. A disk covering a point of the unit circle is in O, and at radius r≤9/40 each disk covers at most 2 asin(r)<2π/13 of that circle, so at least 14 disks are in O. For any nonnegative weighted sum F(d) of half-angles covered at finitely many concentric circles, let F_C, F_M and F_O be rigorous upper bounds on the three ranges. For 26 disks, select one C disk and 14 distinct O disks; the other 11 may be in any group. Therefore

    sum F(d_i) ≤ F_C + 14 F_O + 11 max(F_C,F_M,F_O).

Every sampled circle is covered, so sum F(d_i)≥π sum_j w_j. A strict reverse inequality excludes coverage.

The finite rational data in `radial_28_125_proposal.json` contain 56 newly optimized pairs of circle radii and nonnegative integer weights. All sample radii are strictly greater than r, avoiding whole-circle and d=0 exceptional cases. `radial_28_125_check.py` covers every d from 0 to 1+r with 24,480 rational closed intervals. For each sampled radius, it computes a lower bound on the cosine of the maximum half-angle on the whole interval, using rational endpoint calculations and a lower square-root enclosure at the only possible interior critical point. A cosine Taylor upper polynomial then certifies each proposed rational angular upper bound. Float acos suggests a starting point only; the check and correction are exact. For d>1+r all sampled-circle angles vanish.

The resulting group upper bounds are

    F_C ≤ 30180725031/250000,
    F_M ≤ 15095027437/125000,
    F_O ≤ 60384317183/500000.

In this particular certificate, exact comparison of these three fractions gives `F_O ≥ F_C,F_M`. Hence `max(F_C,F_M,F_O)=F_O` and the displayed upper bound is simply `F_C+25 F_O`. The global 28/125 exclusion can therefore be justified using only the single origin-containing disk and a universal bound `F_O` for every other disk; the independent statement that at least 14 disks meet the boundary is not needed for that global conclusion. The exact B-dependent 9/40 branch arguments below still require their stated physical boundary counts.

Using π>333/106, the strict residual of the displayed group inequality is exactly

    41706129239/26500000 > 0.

The script also checks sin(π/13)>r with rational Taylor bounds, so the 14-boundary capacity step is not numerical. This proves that radius 28/125 cannot cover. Projection of all centers into the compact unit disk and continuity of the minimum covering radius function show that the infimum is attained, making the bound strict.

## Radius 9/40: B=14 and B=17 excluded

For a cover with exactly B physical boundary-intersecting disks, each of the other 26−B disks has either d<1−r or d>1+r. The latter disks have F(d)=0 and can be bounded by max(F_C,F_M). The origin-covering disk belongs to C and cannot be a boundary disk because r<1/2. Thus

    sum F(d_i) ≤ F_C + (25−B) max(F_C,F_M) + B F_O.

`radial_9_40_branches.py 14` and `radial_9_40_branches.py 17` read independent rational weight sets `radial_9_40_B14.json` and `radial_9_40_B17.json`, and prove the reverse strict inequality on 4900 rational intervals. Exact residuals are, respectively,

    B=14: 1303843949129/26500000 > 0,
    B=17: 86449855107/2650000 > 0.

For the remaining range B, the boundary capacity proves B≥14. Boundary disks miss the open concentric disk of radius 1−2r=11/20; the other 26−B disks cover its closure. Since r/(1−2r)=9/22<sin(π/7), the elementary bound r_D(8)≥sin(π/7) forces at least nine non-boundary disks; hence B≤17. Consequently B=15 or 16 in any such cover. The elementary small-cover bound follows because a hypothetical 8-disk unit cover at radius below sin(π/7) needs all eight disks to touch the boundary; with radius <1/2 none can contain the origin.

The sufficient trigonometric inequalities sin(π/13)>9/40 and sin(π/7)>9/22 follow from x−x³/6 with x=333/(106·13) and 333/(106·7), respectively; `verify_reductions.py` checks these rational inequalities.

## Open obligations and scope

These statements do not exclude B=15 or B=16 at radius 9/40 and do not imply r_D(26)≥9/40. Preliminary floating-point LP feasibility persists in both branches after adding several integer-derived radial count constraints; this diagnoses that those specific relaxations are insufficient and is not a geometric cover or proof of feasibility. No claim is made about the original 16-root, 4957-prefix or 344-arithmetic-domain obligations. The new certificates were derived independently of those historical artifacts. Independent second-implementation replay is still requested.

Run with a standard Python interpreter and assertions enabled:

    python round-20261030/lower/radial_28_125_check.py
    python round-20261030/lower/radial_9_40_branches.py 14
    python round-20261030/lower/radial_9_40_branches.py 17
    python round-20261030/lower/verify_reductions.py

The optional `radial_proposal.py` and `radial_branch_proposal.py` generate candidate weights via floating-point SciPy; they are not needed by the exact verification and must not be treated as certificates.

## Frozen input hashes

* `radial_28_125_check.py`: `6c3a85d6424ae765198ff05b0e44803345270c8a885b0b77148c39b781156ba6`
* `radial_28_125_proposal.json`: `3fbff4d8d6e2a8272672746ee7eeef62ac6f494d0bbb2351890aa37d4cd787ad`
* `radial_9_40_branches.py`: `96fef2b466ea2eeb7935542bdb6b529821bc43c3b9cb3ee90621610788e8424d`
* `radial_9_40_B14.json`: `41ca5e8b6444c4bb29afaf285024a0b3a117520ea6505cc9293581ac6f98d54b`
* `radial_9_40_B17.json`: `9f9517dbefa05015b7c05b9bcd233db5469e97754806623c555e63fb625c6b4c`
