/-
DCPN11Core/Combinatorics.lean

Machine-checked (core Lean 4 only, no Mathlib, no `sorry`, no `native_decide`)
finite/combinatorial facts used in the n = 11 source proof (C924).

Source references (repo Liyang1145/DiskCoveringProofs):
* `tools/mathcheck_n11.py` : `FACES`, `oracle_edges()`.
* `docs/N11_CHECK_SCOPE.md` : identities 1-4 (reflection bookkeeping).
* `cover11/.../lead/UNRESTRICTED-PROOF-ASSEMBLY.md` §4 (3-cliques are consecutive
  triples), §4-§5 (hub-degree sum 13 - q, degree-pair ledger).
* `cover11/.../lead/EXACT-ORACLE-INDEX-MAP.md` (raw -> canonical relabelling).

Index conventions follow the Python checker: ring sites 0..8, hubs 9 (= H0) and
10 (= H1); in the oracle graph nodes 0..8 are anchors (switches), 9..19 sites
(site s is node 9+s), 20..30 face witnesses.
-/

namespace DCPCore

/-! ## 1. The eleven Delaunay faces of the attaining configuration (C892) -/

/-- `FACES` from `tools/mathcheck_n11.py`. -/
def faces : List (Nat × Nat × Nat) :=
  [(1, 2, 10), (2, 3, 9), (3, 4, 9), (4, 5, 9), (5, 6, 9),
   (6, 7, 10), (8, 0, 10), (2, 9, 10), (6, 9, 10), (0, 1, 10), (7, 8, 10)]

def sortPair (a b : Nat) : Nat × Nat := (min a b, max a b)

def faceEdges (f : Nat × Nat × Nat) : List (Nat × Nat) :=
  [sortPair f.1 f.2.1, sortPair f.2.1 f.2.2, sortPair f.1 f.2.2]

def edgeOccs : List (Nat × Nat) := faces.flatMap faceEdges

def edgeCount (e : Nat × Nat) : Nat := (edgeOccs.filter (· == e)).length

def distinctEdges : List (Nat × Nat) := edgeOccs.eraseDups

/-- Boundary (convex-hull) edges of the ring: `{k, k+1 mod 9}`. -/
def isHullEdge (e : Nat × Nat) : Bool :=
  (List.range 9).any fun k => e == sortPair k ((k + 1) % 9)

theorem faces_length : faces.length = 11 := by decide

theorem distinctEdges_length : distinctEdges.length = 21 := by decide

/-- Triangulation incidence (checker: "invalid triangulation incidence"):
every hull edge lies in exactly one face, every interior edge in exactly two. -/
theorem face_incidence :
    distinctEdges.all (fun e => edgeCount e == if isHullEdge e then 1 else 2) = true := by
  decide

/-- All nine hull edges occur. -/
theorem hull_edges_present :
    (List.range 9).all (fun k => distinctEdges.contains (sortPair k ((k + 1) % 9))) = true := by
  decide

/-- Euler characteristic of the triangulated disk: V - E + F = 11 - 21 + 11 = 1. -/
theorem euler_disk : 11 + faces.length = distinctEdges.length + 1 := by decide

/-! ## 2. Reflection bookkeeping (N11_CHECK_SCOPE identities 3 and 4)

Reflection in the x-axis sends ring site `k` to `8 - k` and pin `U k` to
`U ((7 - k) mod 9)`; it fixes both hubs. -/

def reflSite (k : Nat) : Nat := 8 - k

def reflPin (k : Nat) : Nat := (16 - k) % 9

/-- The four fan constraints of `f(z)`: `|U1-H1|`, `|U2-H0|`, `|U3-H0|`, `|U8-H1|`. -/
def constraintPins : List (Nat × Nat) := [(1, 10), (2, 9), (3, 9), (8, 10)]

/-- Active fan faces obtained from the constraints and their reflections. -/
def activeFanPins : List (Nat × Nat) :=
  (constraintPins ++ constraintPins.map (fun p => (reflPin p.1, p.2))).eraseDups

theorem reflPin_involutive : (List.range 9).all (fun k => reflPin (reflPin k) == k) = true := by
  decide

theorem reflSite_involutive : (List.range 9).all (fun k => reflSite (reflSite k) == k) = true := by
  decide

/-- Pins and sites are compatible: the reflected pin of edge `{k,k+1}` is the pin of the
reflected edge `{8-(k+1), 8-k}` (for `k ≤ 7`; edge 8 is `{8,0}`, fixed). -/
theorem reflPin_matches_reflSite :
    (List.range 8).all (fun k => reflPin k == reflSite (k + 1)) = true ∧ reflPin 8 = 8 := by
  decide

/-- The seven active fan faces are those with ring edges 1,2,3,4,5,6,8. -/
theorem activeFan_edges :
    (activeFanPins.map Prod.fst).all (fun k => [1, 2, 3, 4, 5, 6, 8].contains k) = true ∧
    [1, 2, 3, 4, 5, 6, 8].all (fun k => (activeFanPins.map Prod.fst).contains k) = true ∧
    activeFanPins.length = 7 := by
  decide

/-- Each active fan pin `(k, h)` is a listed Delaunay face `(k, k+1 mod 9, h)`. -/
theorem activeFan_are_faces :
    activeFanPins.all (fun p => faces.contains (p.1, (p.1 + 1) % 9, p.2)) = true := by
  decide

/-- Central faces `(6,H0,H1)` (fifth constraint) and its mirror `(2,H0,H1)`. -/
theorem central_faces : faces.contains (6, 9, 10) = true ∧ faces.contains (2, 9, 10) = true ∧
    reflSite 6 = 2 := by decide

/-- The two slack faces `(0,1,H1)` and `(7,8,H1)` form one reflection pair. -/
theorem slack_faces : faces.contains (0, 1, 10) = true ∧ faces.contains (7, 8, 10) = true ∧
    reflPin 0 = 7 := by decide

/-- 7 fan + 2 central active + 2 slack = all 11 faces. -/
theorem face_partition : activeFanPins.length + 2 + 2 = faces.length := by decide

/-! ## 3. The canonical oracle graph (C921, `oracle_edges()`) -/

/-- Canonical faces: hub 9 fans over ring edges 0..3, hub 10 over 4..8, central faces at 0, 4. -/
def oracleFaces : List (List Nat) :=
  ((List.range 4).map fun k => [9, k, k + 1]) ++
  ((List.range 5).map fun i => [10, i + 4, (i + 5) % 9]) ++
  [[9, 10, 0], [9, 10, 4]]

/-- Switch edges: site k (node 9+k) to anchors k and k-1. -/
def switchEdges : List (Nat × Nat) :=
  (List.range 9).flatMap fun k => [(9 + k, k), (9 + k, (k + 8) % 9)]

/-- Witness edges: face j's witness (node 20+j) to each site of face j. -/
def witnessEdges : List (Nat × Nat) :=
  (oracleFaces.zipIdx).flatMap fun (f, j) => f.map fun s => (9 + s, 20 + j)

def oracleEdges : List (Nat × Nat) := switchEdges ++ witnessEdges

theorem oracle_counts :
    switchEdges.length = 18 ∧ witnessEdges.length = 33 ∧ oracleEdges.length = 51 ∧
    oracleEdges.eraseDups.length = 51 := by decide

/-- The oracle edge list coincides literally with `oracle_edges()` in the checker. -/
theorem oracle_edges_literal : oracleEdges =
  [(9, 0), (9, 8), (10, 1), (10, 0), (11, 2), (11, 1), (12, 3), (12, 2), (13, 4), (13, 3),
   (14, 5), (14, 4), (15, 6), (15, 5), (16, 7), (16, 6), (17, 8), (17, 7), (18, 20), (9, 20),
   (10, 20), (18, 21), (10, 21), (11, 21), (18, 22), (11, 22), (12, 22), (18, 23), (12, 23),
   (13, 23), (19, 24), (13, 24), (14, 24), (19, 25), (14, 25), (15, 25), (19, 26), (15, 26),
   (16, 26), (19, 27), (16, 27), (17, 27), (19, 28), (17, 28), (9, 28), (18, 29), (19, 29),
   (9, 29), (18, 30), (19, 30), (13, 30)] := by decide

/-- Hub degrees in the surviving class q0(6,7): neighbours of a hub = other sites in its faces. -/
def nbrs (h : Nat) : List Nat :=
  ((oracleFaces.filter (·.contains h)).flatMap id).eraseDups.filter (· != h)

theorem hub_degrees : (nbrs 9).length = 6 ∧ (nbrs 10).length = 7 ∧
    (nbrs 9).length + (nbrs 10).length = 13 - 0 := by decide

/-! ## 4. Raw -> canonical relabelling (EXACT-ORACLE-INDEX-MAP.md): `s = (j - 2) mod 9` -/

def toCanon (j : Nat) : Nat := (j + 7) % 9

/-- Raw active faces of the C891 root: central at 2,6; hub 9 fans 2,3,4,5; hub 10 fans 1,6,8. -/
theorem raw_to_canonical :
    [2, 6].map toCanon = [0, 4] ∧ [2, 3, 4, 5].map toCanon = [0, 1, 2, 3] ∧
    [1, 6, 8].map toCanon = [8, 4, 6] := by decide

/-- Exactly canonical hub-10 fans 5 and 7 are absent from the local carrying network. -/
theorem missing_canonical_fans :
    ([4, 5, 6, 7, 8].filter fun k => !([1, 6, 8].map toCanon).contains k) = [5, 7] := by decide

/-! ## 5. §4 of the assembly: every pairwise-local 3-clique of C9 is a consecutive triple -/

def cdist (i j : Nat) : Nat := min ((i + 9 - j) % 9) ((j + 9 - i) % 9)

def isConsecutiveTriple (i j k : Nat) : Bool :=
  (List.range 9).any fun t =>
    let s := [t, (t + 1) % 9, (t + 2) % 9]
    s.contains i && s.contains j && s.contains k

/-- "Every 3-clique in C9² is a consecutive triple: cyclic gaps sum to 9 and pairwise cyclic
distances ≤ 2 force gaps 1,1,7." -/
theorem clique_consecutive :
    (List.range 9).all (fun i => (List.range 9).all fun j => (List.range 9).all fun k =>
      !(i != j && j != k && i != k && cdist i j ≤ 2 && cdist j k ≤ 2 && cdist i k ≤ 2) ||
        isConsecutiveTriple i j k) = true := by
  decide

/-! ## 6. §5 degree-pair ledger -/

/-- Unordered hub-degree pairs `(q, a, b)`, `3 ≤ a ≤ b`, `a + b = 13 - q`, `q ≤ 1`. -/
def degreePairs : List (Nat × Nat × Nat) :=
  [0, 1].flatMap fun q => (List.range 14).flatMap fun a => (List.range 14).filterMap fun b =>
    if 3 ≤ a && a ≤ b && a + b == 13 - q then some (q, a, b) else none

theorem degreePairs_eq : degreePairs =
    [(0, 3, 10), (0, 4, 9), (0, 5, 8), (0, 6, 7), (1, 3, 9), (1, 4, 8), (1, 5, 7), (1, 6, 6)] := by
  decide

/-- Classes excluded by the full-domain metric certificates (degree three; q1 (4,8),(5,7),(6,6);
q0 (4,9),(5,8)). The remaining class is exactly q0(6,7). -/
def excludedClass (p : Nat × Nat × Nat) : Bool :=
  p.2.1 == 3 || [(1, 4, 8), (1, 5, 7), (1, 6, 6), (0, 4, 9), (0, 5, 8)].contains p

theorem only_q0_6_7_survives : degreePairs.filter (fun p => !excludedClass p) = [(0, 6, 7)] := by
  decide

end DCPCore
