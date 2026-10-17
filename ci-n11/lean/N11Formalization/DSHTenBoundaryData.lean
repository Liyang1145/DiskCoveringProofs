import N11Formalization.DSHTenBoundaryMain

/-!
# DSH-TOPO-C1 — the 36 source segments as Lean data, and the resulting obligation

The ten-boundary exclusion is reduced (C1701, `DSHTenBoundaryMain.lean`) to a certificate whose
only mathematical content is one single-disk continuum inequality per segment.  This file fixes
the **data** of the paid source certificate as a Lean `def`, proves the two *finite* checks
in-kernel (the segments are edge-to-edge from `0` to `7/50`; every weight triple is non-negative),
and exposes the residual obligation

```
C450PerDiskObligation := ∀ s ∈ c450Segs, s.PerDisk
```

so that the remaining work is exactly 36 named inequalities on explicit rational data — no
coverage/combinatorics left.

Provenance of the data (read-only, not modified):
* `research-2026/solo-20260922/directional_low_cover.json` — 2 segments, `pass: true`
  (`e ∈ [0, 0.004] ∪ [0.004, 0.0071]`);
* `research-2026/solo-20260922/directional_e_cover.json` — 34 segments, `pass: true`,
  `all_covered: true` (`e` from `0.0071` to `0.14 = 7/50`);
* extracted verbatim by `evidence/dsh/topology/ten-boundary/extract_segments36.py` into
  `evidence/dsh/topology/ten-boundary/segments36.leandata.txt` (endpoints and weights are the
  exact rationals of the source, decimals like `0.0071` read as `71/10000`).

**Scope label: module/standalone.** Not root-integrated.
-/

set_option autoImplicit false
noncomputable section

namespace N11Formalization

/-! ## 1. A self-contained `List.all` bridge (no dependency on library naming) -/

/-- `l.all p = true` iff `p` holds on every member of `l`. -/
theorem list_all_eq_true {α : Type*} (p : α → Bool) :
    ∀ (l : List α), l.all p = true ↔ ∀ a ∈ l, p a = true
  | [] => by simp
  | a :: t => by
    rw [List.all_cons, Bool.and_eq_true]
    constructor
    · rintro ⟨hp, ht⟩ b hb
      rcases List.mem_cons.mp hb with rfl | hbt
      · exact hp
      · exact (list_all_eq_true p t).mp ht b hbt
    · intro h
      exact ⟨h a (by simp),
        (list_all_eq_true p t).mpr (fun b hb => h b (by simp [hb]))⟩

/-! ## 2. The 36 segments (exact source data) -/

/-- The 36 closed segments of the paid C450 dual certificate, with their exact rational weights. -/
def c450Segs : List TenSeg := [
  { eLo := (0 : ℚ), eHi := (1 : ℚ) / 250,
    a0 := (641363 : ℚ) / 250000, a1 := (0 : ℚ), a2 := (0 : ℚ), a3 := (0 : ℚ),
    b0 := (338103 : ℚ) / 500000, b1 := (-17317 : ℚ) / 1000000, b2 := (31 : ℚ) / 100000, b3 := (-27 : ℚ) / 1000000 },
  { eLo := (1 : ℚ) / 250, eHi := (71 : ℚ) / 10000,
    a0 := (641363 : ℚ) / 250000, a1 := (0 : ℚ), a2 := (0 : ℚ), a3 := (0 : ℚ),
    b0 := (42283 : ℚ) / 62500, b1 := (-48331 : ℚ) / 1000000, b2 := (431 : ℚ) / 500000, b3 := (77 : ℚ) / 1000000 },
  { eLo := (71 : ℚ) / 10000, eHi := (1 : ℚ) / 125,
    a0 := (641363 : ℚ) / 250000, a1 := (0 : ℚ), a2 := (0 : ℚ), a3 := (0 : ℚ),
    b0 := (338529 : ℚ) / 500000, b1 := (-8237 : ℚ) / 125000, b2 := (1741 : ℚ) / 1000000, b3 := (-2 : ℚ) / 15625 },
  { eLo := (1 : ℚ) / 125, eHi := (3 : ℚ) / 250,
    a0 := (641363 : ℚ) / 250000, a1 := (0 : ℚ), a2 := (0 : ℚ), a3 := (0 : ℚ),
    b0 := (677853 : ℚ) / 1000000, b1 := (-87251 : ℚ) / 1000000, b2 := (2711 : ℚ) / 1000000, b3 := (-17 : ℚ) / 200000 },
  { eLo := (3 : ℚ) / 250, eHi := (2 : ℚ) / 125,
    a0 := (641363 : ℚ) / 250000, a1 := (0 : ℚ), a2 := (0 : ℚ), a3 := (0 : ℚ),
    b0 := (339853 : ℚ) / 500000, b1 := (-61173 : ℚ) / 500000, b2 := (667 : ℚ) / 125000, b3 := (-59 : ℚ) / 250000 },
  { eLo := (2 : ℚ) / 125, eHi := (1 : ℚ) / 50,
    a0 := (1279761 : ℚ) / 500000, a1 := (-9833 : ℚ) / 1000000, a2 := (-1209 : ℚ) / 200000, a3 := (-1141 : ℚ) / 500000,
    b0 := (344093 : ℚ) / 500000, b1 := (-14769 : ℚ) / 100000, b2 := (14883 : ℚ) / 1000000, b3 := (1717 : ℚ) / 1000000 },
  { eLo := (1 : ℚ) / 50, eHi := (3 : ℚ) / 125,
    a0 := (638997 : ℚ) / 250000, a1 := (-3923 : ℚ) / 250000, a2 := (-913 : ℚ) / 100000, a3 := (-1523 : ℚ) / 500000,
    b0 := (694981 : ℚ) / 1000000, b1 := (-88593 : ℚ) / 500000, b2 := (22417 : ℚ) / 1000000, b3 := (253 : ℚ) / 125000 },
  { eLo := (3 : ℚ) / 125, eHi := (7 : ℚ) / 250,
    a0 := (319043 : ℚ) / 125000, a1 := (-1083 : ℚ) / 50000, a2 := (-12181 : ℚ) / 1000000, a3 := (-3781 : ℚ) / 1000000,
    b0 := (702603 : ℚ) / 1000000, b1 := (-517 : ℚ) / 2500, b2 := (7717 : ℚ) / 250000, b3 := (2069 : ℚ) / 1000000 },
  { eLo := (7 : ℚ) / 250, eHi := (4 : ℚ) / 125,
    a0 := (2546909 : ℚ) / 1000000, a1 := (-1923 : ℚ) / 62500, a2 := (-9061 : ℚ) / 500000, a3 := (-6211 : ℚ) / 1000000,
    b0 := (356397 : ℚ) / 500000, b1 := (-233439 : ℚ) / 1000000, b2 := (4319 : ℚ) / 100000, b3 := (3449 : ℚ) / 1000000 },
  { eLo := (4 : ℚ) / 125, eHi := (9 : ℚ) / 250,
    a0 := (318087 : ℚ) / 125000, a1 := (-6853 : ℚ) / 200000, a2 := (-9577 : ℚ) / 500000, a3 := (-5873 : ℚ) / 1000000,
    b0 := (11257 : ℚ) / 15625, b1 := (-133077 : ℚ) / 500000, b2 := (51583 : ℚ) / 1000000, b3 := (1959 : ℚ) / 1000000 },
  { eLo := (9 : ℚ) / 250, eHi := (1 : ℚ) / 25,
    a0 := (2536217 : ℚ) / 1000000, a1 := (-1507 : ℚ) / 31250, a2 := (-6701 : ℚ) / 250000, a3 := (-8123 : ℚ) / 1000000,
    b0 := (11487 : ℚ) / 15625, b1 := (-144467 : ℚ) / 500000, b2 := (33703 : ℚ) / 500000, b3 := (1141 : ℚ) / 500000 },
  { eLo := (1 : ℚ) / 25, eHi := (11 : ℚ) / 250,
    a0 := (126763 : ℚ) / 50000, a1 := (-24953 : ℚ) / 500000, a2 := (-1407 : ℚ) / 50000, a3 := (-549 : ℚ) / 62500,
    b0 := (46443 : ℚ) / 62500, b1 := (-162109 : ℚ) / 500000, b2 := (78211 : ℚ) / 1000000, b3 := (221 : ℚ) / 200000 },
  { eLo := (11 : ℚ) / 250, eHi := (6 : ℚ) / 125,
    a0 := (316023 : ℚ) / 125000, a1 := (-12353 : ℚ) / 200000, a2 := (-35689 : ℚ) / 1000000, a3 := (-2347 : ℚ) / 200000,
    b0 := (378969 : ℚ) / 500000, b1 := (-35023 : ℚ) / 100000, b2 := (96127 : ℚ) / 1000000, b3 := (261 : ℚ) / 250000 },
  { eLo := (6 : ℚ) / 125, eHi := (13 : ℚ) / 250,
    a0 := (1262853 : ℚ) / 500000, a1 := (-65913 : ℚ) / 1000000, a2 := (-2397 : ℚ) / 62500, a3 := (-12797 : ℚ) / 1000000,
    b0 := (768919 : ℚ) / 1000000, b1 := (-384303 : ℚ) / 1000000, b2 := (27543 : ℚ) / 250000, b3 := (-633 : ℚ) / 1000000 },
  { eLo := (13 : ℚ) / 250, eHi := (7 : ℚ) / 125,
    a0 := (1260629 : ℚ) / 500000, a1 := (-9169 : ℚ) / 125000, a2 := (-43591 : ℚ) / 1000000, a3 := (-15237 : ℚ) / 1000000,
    b0 := (97841 : ℚ) / 125000, b1 := (-20801 : ℚ) / 50000, b2 := (25729 : ℚ) / 200000, b3 := (-2289 : ℚ) / 1000000 },
  { eLo := (7 : ℚ) / 125, eHi := (3 : ℚ) / 50,
    a0 := (2516033 : ℚ) / 1000000, a1 := (-82023 : ℚ) / 1000000, a2 := (-6163 : ℚ) / 125000, a3 := (-221 : ℚ) / 12500,
    b0 := (79807 : ℚ) / 100000, b1 := (-44739 : ℚ) / 100000, b2 := (29563 : ℚ) / 200000, b3 := (-4237 : ℚ) / 1000000 },
  { eLo := (3 : ℚ) / 50, eHi := (8 : ℚ) / 125,
    a0 := (1255837 : ℚ) / 500000, a1 := (-44577 : ℚ) / 500000, a2 := (-13717 : ℚ) / 250000, a3 := (-10379 : ℚ) / 500000,
    b0 := (406707 : ℚ) / 500000, b1 := (-240633 : ℚ) / 500000, b2 := (33789 : ℚ) / 200000, b3 := (-6647 : ℚ) / 1000000 },
  { eLo := (8 : ℚ) / 125, eHi := (17 : ℚ) / 250,
    a0 := (501443 : ℚ) / 200000, a1 := (-48167 : ℚ) / 500000, a2 := (-60391 : ℚ) / 1000000, a3 := (-11929 : ℚ) / 500000,
    b0 := (82963 : ℚ) / 100000, b1 := (-51559 : ℚ) / 100000, b2 := (95227 : ℚ) / 500000, b3 := (-453 : ℚ) / 50000 },
  { eLo := (17 : ℚ) / 250, eHi := (9 : ℚ) / 125,
    a0 := (500141 : ℚ) / 200000, a1 := (-106689 : ℚ) / 1000000, a2 := (-13647 : ℚ) / 200000, a3 := (-28289 : ℚ) / 1000000,
    b0 := (424413 : ℚ) / 500000, b1 := (-68653 : ℚ) / 125000, b2 := (108613 : ℚ) / 500000, b3 := (-6511 : ℚ) / 500000 },
  { eLo := (9 : ℚ) / 125, eHi := (19 : ℚ) / 250,
    a0 := (499617 : ℚ) / 200000, a1 := (-111007 : ℚ) / 1000000, a2 := (-17749 : ℚ) / 250000, a3 := (-14717 : ℚ) / 500000,
    b0 := (21623 : ℚ) / 25000, b1 := (-14711 : ℚ) / 25000, b2 := (238913 : ℚ) / 1000000, b3 := (-18151 : ℚ) / 1000000 },
  { eLo := (19 : ℚ) / 250, eHi := (2 : ℚ) / 25,
    a0 := (2472381 : ℚ) / 1000000, a1 := (-153577 : ℚ) / 1000000, a2 := (-97517 : ℚ) / 1000000, a3 := (-39747 : ℚ) / 1000000,
    b0 := (452251 : ℚ) / 500000, b1 := (-598119 : ℚ) / 1000000, b2 := (17659 : ℚ) / 62500, b3 := (-23839 : ℚ) / 1000000 },
  { eLo := (2 : ℚ) / 25, eHi := (21 : ℚ) / 250,
    a0 := (2437379 : ℚ) / 1000000, a1 := (-106253 : ℚ) / 500000, a2 := (-125111 : ℚ) / 1000000, a3 := (-21421 : ℚ) / 500000,
    b0 := (118933 : ℚ) / 125000, b1 := (-597053 : ℚ) / 1000000, b2 := (319549 : ℚ) / 1000000, b3 := (-17431 : ℚ) / 500000 },
  { eLo := (21 : ℚ) / 250, eHi := (11 : ℚ) / 125,
    a0 := (2402767 : ℚ) / 1000000, a1 := (-53503 : ℚ) / 200000, a2 := (-4563 : ℚ) / 31250, a3 := (-10659 : ℚ) / 250000,
    b0 := (995657 : ℚ) / 1000000, b1 := (-600839 : ℚ) / 1000000, b2 := (174061 : ℚ) / 500000, b3 := (-5837 : ℚ) / 125000 },
  { eLo := (11 : ℚ) / 125, eHi := (23 : ℚ) / 250,
    a0 := (2361027 : ℚ) / 1000000, a1 := (-318149 : ℚ) / 1000000, a2 := (-81607 : ℚ) / 500000, a3 := (-26327 : ℚ) / 500000,
    b0 := (522331 : ℚ) / 500000, b1 := (-306827 : ℚ) / 500000, b2 := (377783 : ℚ) / 1000000, b3 := (-2129 : ℚ) / 40000 },
  { eLo := (23 : ℚ) / 250, eHi := (12 : ℚ) / 125,
    a0 := (1162893 : ℚ) / 500000, a1 := (-71319 : ℚ) / 200000, a2 := (-10451 : ℚ) / 62500, a3 := (-54393 : ℚ) / 1000000,
    b0 := (135621 : ℚ) / 125000, b1 := (-19723 : ℚ) / 31250, b2 := (393177 : ℚ) / 1000000, b3 := (-12131 : ℚ) / 200000 },
  { eLo := (12 : ℚ) / 125, eHi := (1 : ℚ) / 10,
    a0 := (14281 : ℚ) / 6250, a1 := (-11689 : ℚ) / 31250, a2 := (-153409 : ℚ) / 1000000, a3 := (-68827 : ℚ) / 1000000,
    b0 := (141171 : ℚ) / 125000, b1 := (-66779 : ℚ) / 100000, b2 := (50391 : ℚ) / 125000, b3 := (-1169 : ℚ) / 20000 },
  { eLo := (1 : ℚ) / 10, eHi := (13 : ℚ) / 125,
    a0 := (2250997 : ℚ) / 1000000, a1 := (-396597 : ℚ) / 1000000, a2 := (-139349 : ℚ) / 1000000, a3 := (-67941 : ℚ) / 1000000,
    b0 := (145631 : ℚ) / 125000, b1 := (-694609 : ℚ) / 1000000, b2 := (20341 : ℚ) / 50000, b3 := (-63619 : ℚ) / 1000000 },
  { eLo := (13 : ℚ) / 125, eHi := (27 : ℚ) / 250,
    a0 := (1110529 : ℚ) / 500000, a1 := (-438427 : ℚ) / 1000000, a2 := (-8223 : ℚ) / 62500, a3 := (-45257 : ℚ) / 1000000,
    b0 := (1195251 : ℚ) / 1000000, b1 := (-4413 : ℚ) / 6250, b2 := (50913 : ℚ) / 125000, b3 := (-81867 : ℚ) / 1000000 },
  { eLo := (27 : ℚ) / 250, eHi := (14 : ℚ) / 125,
    a0 := (44527 : ℚ) / 20000, a1 := (-212969 : ℚ) / 500000, a2 := (-59621 : ℚ) / 1000000, a3 := (28417 : ℚ) / 1000000,
    b0 := (1190153 : ℚ) / 1000000, b1 := (-365971 : ℚ) / 500000, b2 := (21743 : ℚ) / 62500, b3 := (-110323 : ℚ) / 1000000 },
  { eLo := (14 : ℚ) / 125, eHi := (29 : ℚ) / 250,
    a0 := (2208767 : ℚ) / 1000000, a1 := (-434279 : ℚ) / 1000000, a2 := (-36759 : ℚ) / 1000000, a3 := (42687 : ℚ) / 1000000,
    b0 := (603827 : ℚ) / 500000, b1 := (-755167 : ℚ) / 1000000, b2 := (168521 : ℚ) / 500000, b3 := (-23089 : ℚ) / 200000 },
  { eLo := (29 : ℚ) / 250, eHi := (3 : ℚ) / 25,
    a0 := (21903 : ℚ) / 10000, a1 := (-4483 : ℚ) / 10000, a2 := (-21009 : ℚ) / 1000000, a3 := (54999 : ℚ) / 1000000,
    b0 := (612693 : ℚ) / 500000, b1 := (-38707 : ℚ) / 50000, b2 := (331669 : ℚ) / 1000000, b3 := (-119577 : ℚ) / 1000000 },
  { eLo := (3 : ℚ) / 25, eHi := (31 : ℚ) / 250,
    a0 := (543489 : ℚ) / 250000, a1 := (-228903 : ℚ) / 500000, a2 := (-2217 : ℚ) / 1000000, a3 := (13601 : ℚ) / 200000,
    b0 := (1240349 : ℚ) / 1000000, b1 := (-793773 : ℚ) / 1000000, b2 := (161441 : ℚ) / 500000, b3 := (-61847 : ℚ) / 500000 },
  { eLo := (31 : ℚ) / 250, eHi := (16 : ℚ) / 125,
    a0 := (1078281 : ℚ) / 500000, a1 := (-118223 : ℚ) / 250000, a2 := (2337 : ℚ) / 250000, a3 := (7861 : ℚ) / 100000,
    b0 := (39243 : ℚ) / 31250, b1 := (-404747 : ℚ) / 500000, b2 := (63913 : ℚ) / 200000, b3 := (-126717 : ℚ) / 1000000 },
  { eLo := (16 : ℚ) / 125, eHi := (33 : ℚ) / 250,
    a0 := (267611 : ℚ) / 125000, a1 := (-485807 : ℚ) / 1000000, a2 := (1083 : ℚ) / 50000, a3 := (90029 : ℚ) / 1000000,
    b0 := (79307 : ℚ) / 62500, b1 := (-206147 : ℚ) / 250000, b2 := (314617 : ℚ) / 1000000, b3 := (-129707 : ℚ) / 1000000 },
  { eLo := (33 : ℚ) / 250, eHi := (17 : ℚ) / 125,
    a0 := (2125163 : ℚ) / 1000000, a1 := (-313 : ℚ) / 625, a2 := (1533 : ℚ) / 50000, a3 := (100773 : ℚ) / 1000000,
    b0 := (640781 : ℚ) / 500000, b1 := (-837559 : ℚ) / 1000000, b2 := (12459 : ℚ) / 40000, b3 := (-8283 : ℚ) / 62500 },
  { eLo := (17 : ℚ) / 125, eHi := (7 : ℚ) / 50,
    a0 := (26531 : ℚ) / 12500, a1 := (-49061 : ℚ) / 100000, a2 := (28973 : ℚ) / 500000, a3 := (59453 : ℚ) / 500000,
    b0 := (640343 : ℚ) / 500000, b1 := (-856119 : ℚ) / 1000000, b2 := (291739 : ℚ) / 1000000, b3 := (-33207 : ℚ) / 250000 }
]

/-! ## 3. The two finite checks, discharged in the kernel -/

/-- The 36 segments are edge-to-edge and cover `[0, 7/50]`.  A finite rational computation. -/
theorem c450Segs_chain : Chain 0 c450Segs = some (7 / 50) := by decide +kernel

/-- The weight-triple non-negativity check, as a computable `Bool`. -/
def segNonnegCheck (s : TenSeg) : Bool :=
  decide (|s.a1| + |s.a2| + |s.a3| ≤ s.a0) && decide (|s.b1| + |s.b2| + |s.b3| ≤ s.b0)

/-- Every segment's two weight functions are non-negative (`a0 ≥ Σ|a_k|`). -/
theorem c450Segs_nonneg :
    ∀ s ∈ c450Segs, |s.a1| + |s.a2| + |s.a3| ≤ s.a0 ∧ |s.b1| + |s.b2| + |s.b3| ≤ s.b0 := by
  have h := (list_all_eq_true segNonnegCheck c450Segs).mp
    (show c450Segs.all segNonnegCheck = true from by decide +kernel)
  intro s hs
  have h2 := h s hs
  simpa only [segNonnegCheck, Bool.and_eq_true, decide_eq_true_eq] using h2

/-! ## 4. The residual obligation and its consumers -/

/-- **The residual obligation**: the 36 per-segment per-disk continuum inequalities.  This is the
whole remaining mathematical content of the ten-boundary exclusion. -/
def C450PerDiskObligation : Prop := ∀ s ∈ c450Segs, s.PerDisk

/-- The obligation assembles into a certificate. -/
def c450Cert_of_obligation (h : C450PerDiskObligation) : TenBoundaryCert :=
  ⟨c450Segs, c450Segs_chain, c450Segs_nonneg, h⟩

/-- The obligation implies the source atom. -/
theorem c450Atom_of_obligation (h : C450PerDiskObligation) : C450Atom :=
  c450Atom_of_cert (c450Cert_of_obligation h)

/-- Ten-boundary exclusion from the 36 obligations, `r ≤ 19/50` form. -/
theorem not_card_boundaryIdx_eq_ten_of_obligation (h : C450PerDiskObligation)
    {c : Fin 11 → Point} {r : ℝ} (hr : r ≤ 19 / 50) (hc : Covers c r) :
    Fintype.card (BoundaryIdx c r) ≠ 10 :=
  not_card_boundaryIdx_eq_ten_of_cert (c450Cert_of_obligation h) hr hc

/-- Ten-boundary exclusion at the paid source-root interval, from the 36 obligations. -/
theorem not_card_boundaryIdx_eq_ten_of_obligation_lt_sourceRadius (h : C450PerDiskObligation)
    {c : Fin 11 → Point} {r : ℝ} (hr : r < SourceExactRoot.sourceRadius) (hc : Covers c r) :
    Fintype.card (BoundaryIdx c r) ≠ 10 :=
  not_card_boundaryIdx_eq_ten_of_lt_sourceRadius (c450Cert_of_obligation h) hr hc

/-- **Exactly nine boundary disks at the paid source-root interval**, from the 36 obligations. -/
theorem card_boundaryIdx_eq_nine_of_obligation_lt_sourceRadius (h : C450PerDiskObligation)
    {c : Fin 11 → Point} {r : ℝ} (hr : r < SourceExactRoot.sourceRadius) (hc : Covers c r) :
    Fintype.card (BoundaryIdx c r) = 9 :=
  card_boundaryIdx_eq_nine_of_lt_sourceRadius (c450Cert_of_obligation h) hr hc

end N11Formalization

end

#print axioms N11Formalization.list_all_eq_true
#print axioms N11Formalization.c450Segs_chain
#print axioms N11Formalization.c450Segs_nonneg
#print axioms N11Formalization.c450Atom_of_obligation
#print axioms N11Formalization.card_boundaryIdx_eq_nine_of_obligation_lt_sourceRadius
#check @N11Formalization.c450Segs
#check @N11Formalization.C450PerDiskObligation
#check @N11Formalization.c450Atom_of_obligation
#check @N11Formalization.not_card_boundaryIdx_eq_ten_of_obligation_lt_sourceRadius
#check @N11Formalization.card_boundaryIdx_eq_nine_of_obligation_lt_sourceRadius
