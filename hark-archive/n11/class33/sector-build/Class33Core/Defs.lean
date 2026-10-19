/- Class33 core-Lean pre-validation: transcribed WIP canonical definitions (no Mathlib).
   Labels are Nat (Fin 11 values); faces/edges are SORTED Lists. NOT Lean credit. -/
namespace Class33Core

def insert3 (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insert3 x ys
def sortL : List Nat → List Nat
  | [] => []
  | x :: xs => insert3 x (sortL xs)

-- ActualRingLinkBoundaryData / ActualQ1CoreCycle / ActualOrderedMetricGraphs
def nextSite (i : Nat) : Nat := (i+1) % 9
def coreSite0 (i : Nat) : Nat := (0 + (i+1)) % 9
def q1Fan (k m i : Nat) : List Nat :=
  sortL [coreSite0 ((i+k) % 8), coreSite0 (((i+k) % 8 + 1) % 8), if i < m then 9 else 10]
def centralFace (i : Nat) : List Nat := sortL [9,10,i]
def q1Ear : List Nat := [0,1,8]
def q1FacesL (k m : Nat) : List (List Nat) :=
  (List.range 8).map (q1Fan k m) ++ [centralFace (coreSite0 k), centralFace (coreSite0 ((m+k) % 8)), q1Ear]
def cycleEdge (k : Nat) : List Nat := sortL [k, nextSite k]
def q0Fan (m i : Nat) : List Nat := sortL [i, nextSite i, if i < m then 9 else 10]
def q0FacesL (m : Nat) : List (List Nat) := (List.range 9).map (q0Fan m) ++ [centralFace 0, centralFace m]
def earGapsL (e : Nat) : List Nat := [(e+7) % 9, (e+8) % 9, e]
def inOutsideGaps (e i : Nat) : Bool := !((earGapsL e).contains i)
def stationWeight (i : Nat) : Rat := if i < 9 then 1 else 2
-- Interval/Trig.lean, MetricAreaRationalCertificate.lean, ActualCanonicalSharedMomentConsumer.lean
def piLo : Rat := 314159265358979323846 / 10 ^ 20
def piHi : Rat := 314159265358979323847 / 10 ^ 20
def piProductUpper (b : Rat) : Rat := b * (if b < 0 then piLo else piHi)
def sharpAlpha : Rat := 863314/1000000

structure Table where
  faces : List (List Nat)          -- the 11 faces (sorted triples)
  edges : List (List Nat)          -- the 21 face edges (sorted pairs)
  mu : Nat → Rat
  kap : List Nat → Rat
  sideFirst : List Nat → Rat
  sideSecond : List Nat → Rat
  faceMask : List Nat → Nat → Rat  -- (sorted face, slot)
  switchMask : Nat → Rat
  leftFirst : Nat → Rat
  leftSecond : Nat → Rat
  rightFirst : Nat → Rat
  rightSecond : Nat → Rat
  width : Rat
  eta : Rat

def label (f : List Nat) (s : Nat) : Nat := f.getD s 0      -- s-th smallest (f sorted)
def flagEdge (f : List Nat) (s : Nat) : List Nat := f.erase (label f s)
def lookupQ (l : List (List Nat × Rat)) (e : List Nat) : Rat := (l.lookup e).getD 0
def lookupN (l : List (Nat × Rat)) (i : Nat) : Rat := (l.lookup i).getD 0
def sumL (l : List Rat) : Rat := l.foldl (· + ·) 0

namespace Table
variable (T : Table)
def faceP (f : List Nat) (s : Nat) : Rat := -T.mu (label f s) - T.kap (flagEdge f s)
def faceQ (f : List Nat) (s : Nat) : Rat := T.faceMask f s * T.sideSecond (flagEdge f s)
def faceB (f : List Nat) (s : Nat) : Rat := T.faceMask f s * T.sideFirst (flagEdge f s)
def switchP (i : Nat) : Rat := sumL ((cycleEdge i).map T.mu) - T.kap (cycleEdge i)
def switchQ (i : Nat) : Rat := T.switchMask i * T.sideSecond (cycleEdge i)
def switchB (i : Nat) : Rat := T.switchMask i * T.sideFirst (cycleEdge i)
def switchD2 (i : Nat) : Rat := T.leftSecond i + T.rightSecond ((i+8) % 9)
def switchD1 (i : Nat) : Rat := T.leftFirst i + T.rightFirst ((i+8) % 9)
def sectorC (ear i : Nat) : Rat := T.width + (if inOutsideGaps ear i then T.eta else 0)
def edgeSum (e : List Nat) : Rat :=
  sumL (T.faces.flatMap (fun f => [0,1,2].map (fun s => if flagEdge f s = e then T.faceMask f s else 0)))
def switchSum (e : List Nat) : Rat :=
  sumL ((List.range 9).map (fun k => if cycleEdge k = e then T.switchMask k else 0))
def balancedB : Bool := T.edges.all (fun e => T.edgeSum e + T.switchSum e == 0)
def edgesAreFlagEdgesB : Bool :=
  T.edges.all (fun e => T.faces.any (fun f => [0,1,2].any (fun s => flagEdge f s == e))) &&
  T.faces.all (fun f => [0,1,2].all (fun s => T.edges.contains (flagEdge f s))) &&
  T.edges.length == 21
def kapNonnegB : Bool := T.edges.all (fun e => decide (0 ≤ T.kap e))
def constantCoeff : Rat :=
  sumL ((List.range 11).map (fun i => stationWeight i * T.mu i)) + sumL (T.edges.map T.kap) - 2*T.width - 2*T.eta
def sharpConstantUpper (alpha : Rat) : Rat := piProductUpper T.constantCoeff + 2*alpha*T.eta
def totalUpper (alpha : Rat) (faceMax : List Rat) (switchMax sectorMax : List Rat) : Rat :=
  T.sharpConstantUpper alpha + sumL faceMax + sumL switchMax + sumL sectorMax
end Table

def sameFacesB (k m : Nat) (fs : List (List Nat)) : Bool :=
  let c := q1FacesL k m
  fs.length == 11 && c.length == 11 && fs.all (c.contains ·) && c.all (fs.contains ·) &&
  fs.all (fun f => f.length == 3 && f == sortL f) && (fs.eraseDups).length == 11

def sameFacesQ0B (m : Nat) (fs : List (List Nat)) : Bool :=
  let c := q0FacesL m
  fs.length == 11 && c.length == 11 && fs.all (c.contains ·) && c.all (fs.contains ·) &&
  fs.all (fun f => f.length == 3 && f == sortL f) && (fs.eraseDups).length == 11

end Class33Core
