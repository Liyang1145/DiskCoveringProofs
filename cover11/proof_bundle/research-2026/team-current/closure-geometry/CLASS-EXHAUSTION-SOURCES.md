# CLASS-EXHAUSTION-SOURCES — corrected source ledger

**Correction notice.** My previous version reported `GAP-A` ("the `q = 1` sub-classes
`(5,7)`/`(4,8)` are covered by no certificate") and omitted `(4,9)` from the `q = 0`
row. **Both were my reading errors, not source gaps:**

* `q1` is excluded in full by the *combination* C809 + C812 + C813 + C817 (as
  `lead/Q1-BALANCED-EXCLUSION.md` §2–3 states), not by C818 alone: C817 covers
  `(5,7)`, C813 the degree-4 members, C812 the degree-3 members, C809 the `q ≥ 2`
  members.
* `q0(4,9)` is excluded by **C819** (`lead/Q0-CLOSURE-EXCLUSIONS.md` §3;
  `certify_q0_moments.py 0 2`, upper bound `2.97871288… < π`).

I re-read `C809, C812, C813, C817, C819` with `claim_get` before writing this
version. Only the ledger is corrected; **no invented correspondences**.

---

## 1. The ledger (registered scope only)

| claim | status | registered content (abridged) | scope as registered |
|---|---|---|---|
| **C809** | `proved-exact`, reviewed | five-ring star lemma (no ring disk meets ≥ 4 others; rational `arccos(53/775) < 1.51`), `q = 2` excluded by the forbidden 4-neighbour star, and with the two-triple lemma (`q ≤ 2`) hence **`q ≤ 1`**, `K = 13 − q ∈ {12,13}` | all `r ≤ 19/50`, 9+2 branch |
| **C812** | `proved-interval` | both refined hub degrees **`≥ 4`**; hence `q = 0` permits only `(4,9),(5,8),(6,7)` and `q = 1` only `(4,8),(5,7),(6,6)`; excludes degree 3 incl. degeneracies | entire `r ≤ .38` 9+2 branch |
| **C813** | `proved-interval` | **no degree-4 hub in the `q = 1` class**; with C812 only `q=0: (4,9),(5,8),(6,7)` and `q=1: (5,7),(6,6)` remain | all `q1` degree-4 placements (8 ear-relative + hub swaps) |
| **C817** | `proved-interval` | every `q1` cover must have pair **`(6,6)`**; **all `(5,7)` placements excluded** (starts 0,1,2,3 give `3.135372, 3.116720, 3.090707, 3.089278 < π`; start 7 by C815) | all `q1` degree-`(5,7)` graphs |
| **C818** | `proved-interval` | both remaining `q1` degree-`(6,6)` orbits impossible (`3.13549360…`, `3.13981254… < π`) | all `q1` graphs |
| **C819** | `proved-interval` | **`q0(4,9)` impossible** (`2.97871288… < π`), `η ≡ 0` | all `q0` degree-`(4,9)` graphs |
| **k3** = `q0(5,8)` | closure certificate | `3.09579300… < π` | `q0(5,8)` |
| **k4** = `q0(6,7)`, `r ≤ 3/8` | closure certificate | `3.10878894… < π` | `q0(6,7)` at `r ≤ 3/8` |
| transfer | RTMD | the single-radius certificates transfer to their claimed `r`-ranges | — |

**Coverage is complete, exactly as the registered scopes say:**

```
   q = 0 :  (4,9) C819    |   (5,8) k3            |   (6,7) k4 (r ≤ 3/8)
   q = 1 :  (4,8) C812 (deg≥4) + C813 (no deg 4)  |   (5,7) C817   |   (6,6) C818
   q ≥ 2 :  C809 (q ≤ 1, with the two-triple lemma)
```

---

## 2. Remaining items (registered non-claims and pending items only)

| id | item | exact registered position |
|---|---|---|
| **GAP-1** | a registered formula relating `K = k_1+k_2 = 13 − q`, `q`, and the **hub degrees** | C801 registers `k_j = m_j + 3`, `K = 13 − q`, `q = c`, and "`K = 13 − q ≥ 11`", but **no formula for the hub degree** `d_j`. The registered pairs in C812 satisfy `d_1 + d_2 = 13 − q` (e.g. `(4,9)` and `(5,8)` and `(6,7)` all sum to 13 at `q = 0`; `(4,8),(5,7),(6,6)` all sum to 12 at `q = 1`), and a combinatorial derivation of that relation is **not** in the sources I read — my earlier attempt (`19 − q`) contradicted the registered pairs and is withdrawn. This is a labelling/documentation item only: every class is excluded by its registered scope regardless. |
| **GAP-2** | realizability of `q = 1` | registered non-claim of C801 and of C809 ("NOT CLAIMED: exclusion or realizability of `q ∈ {0,1}`"); not needed for the exhaustion |
| **GAP-3** | C799 locality (`proved-exact`) independent review pending | used as premise (P2) by the (E7) chain |
| **GAP-4** | C801's premise (P3) | C797, **superseded by C802** (reviewed), conditional on C450's per-single-disk capacity certificate |
| **GAP-5** | **`q0(6,7)` for `3/8 < r ≤ 19/50`** | the open class: k4 covers only `r ≤ 3/8`. This is the real remaining object |

---

## 3. Chain premises (unchanged from the earlier version, kept for the record)

`E1` C450/C451 → `E2` ARC-COORD ledger → `E3` C464 inner root → `E4` VBR cellulation
interface §1–§3 → `E5` C799 locality → `E6` C802 hub adjacency → `E7a` C801/§2a ears
`q ≤ 4` → `E7b` §2b two-triple `q ≤ 2` → `E7c` §2c star lemma `q ≤ 1` (all three
stages now registered as C809) → `E8` the degree-pair certificates of §1 above.
Locations: `solo-20260922/N11-LOW-RADIUS-REDUCTION.md`, `M10-038-EXCLUSION.md`,
`team-max-20260922/n11-structure/ARC-COORD.md`, `solo-20260922/INNER-ROOT-DOMINANCE.md`,
`lead/VORONOI-BOUNDARY-REDUCTION.md` (incl. its "Payoff" non-claims),
`flash-structure/LOCALITY-LEMMA-RING.md`,
`flash-structure/AUDIT-HUB-EDGE-BRIDGE-AND-Q-CLASSES.md` Part 1,
`lead/HUB-ADJACENCY-DUAL.md`, `lead/DUAL-SEMANTIC-AND-ADJACENCY-AUDIT.md`,
`flash-structure/GLOBAL-TOPOLOGICAL-REDUCTION.md` §2a–§4.

Not a gap (verified in the sources): `q ≤ 4` (8-gon lemma over all
`Catalan(6) = 132` triangulations, plus ear-set counts `1, 9, 27, 30, 9`); `q ≤ 2`
and `q ≤ 1` (C809, union-measure capacity with the rational `53/775` certificate);
non-trivalent configurations (refinement; ring-only faces of a refinement are still
consecutive triples since the clique number of `C_9²` is 3; `q` is explicitly not
claimed refinement-invariant).

No claim registered; no subagent; no lead file modified.
