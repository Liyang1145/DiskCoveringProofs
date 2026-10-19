"""Emit core-Lean (no Mathlib) pre-validation modules for the two q1-balanced representative tables.
Output: class33/lean-core/Class33Core/{Defs,Rep7,Rep1}.lean.
The definitions in Defs.lean transcribe (over Nat labels / sorted Lists / core Rat) the WIP definitions
q1Fan, q1Faces, q1Ear, coreSite, cycleEdge, canonicalLabel (s-th smallest), flagEdge, canonicalFace{P,Q,B},
canonicalSwitch{P,Q,B,D2,D1}, canonicalSectorC, CanonicalMaskBalancedQ, canonicalConstantCoeffQ,
piProductUpper, canonicalTotalUpperQ.  Pre-validation only."""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N11
import json, re, sys, os
from fractions import Fraction as F
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent)); import rep_tables as RT
ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'lean-core' / 'Class33Core'; OUT.mkdir(parents=True, exist_ok=True)
WIP = Path(DCP_N11+'/wip/lean/N11Formalization')
def q(x): x = F(x); return f'({x.numerator}/{x.denominator} : Rat)' if x.denominator != 1 else f'({x.numerator} : Rat)'
def lst(xs): return '[' + ','.join(xs) + ']'
def nl(l): return '[' + ','.join(map(str, l)) + ']'
def wr(path, s):
    tmp = str(path) + '.tmp'; Path(tmp).write_text(s); os.replace(tmp, path)

DEFS = r'''/- Class33 core-Lean pre-validation: transcribed WIP canonical definitions (no Mathlib).
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
'''
wr(OUT / 'Defs.lean', DEFS)

src = (WIP / 'SharedMomentConcreteSwitchBatch.lean').read_text()
batch = {}
for m in re.finditer(r'def start0_switch(\d)_(p|q|b|d2|d1|bound) : ℚ := \((.*?) : ℚ\)', src):
    batch.setdefault(int(m.group(1)), {})[m.group(2)] = F(m.group(3).strip('()'))
budget = json.loads((ROOT / 'data' / 'budget.json').read_text())

for start, k, cls, mod in [(0, 7, 'q1bal', 'Rep7'), (2, 1, 'q1bal', 'Rep1'), (0, 2, 'q0', 'Q0M2')]:
    T = RT.build(start, k, cls)
    faces = sorted([sorted(f) for f in T['Fs']])
    edges = sorted([sorted(e) for e in T['E']])
    def eL(d): return lst(f'({nl(sorted(e))},{q(v)})' for e, v in sorted(d.items(), key=lambda x: sorted(x[0])))
    def nL(d): return lst(f'({i},{q(v)})' for i, v in sorted(d.items()))
    fm = lst(f'(({nl(sorted(f))},{s}),{q(v)})' for (f, s), v in sorted(T['faceMask'].items(), key=lambda x: (sorted(x[0][0]), x[0][1])))
    B = budget[(f'k{k}' if cls == 'q1bal' else f'q0m{k}') + '_den1000000']
    faceMax = [F(B['faceMax'][','.join(map(str, f))]) for f in faces]
    swMax = [F(B['switchMax'][str(j)]) for j in range(9)]
    secMax = [F(B['sectorMax'][str(j)]) for j in range(9)]
    title = (f'Representative q1-balanced table, Lean cut k={k}, m=4 (historical start{start}).\n   Data: 9-place coefficients of shared_moment_dense_certificate_{start}_4.json relabelled ring h -> h-1 mod 9.'
             if cls == 'q1bal' else f'Q0 class table, Lean q0Faces {k} (hub degrees (4,9); historical span {k}).\n   Data: 9-place coefficients of q0_moment_dual_certificate_{start}_{k}.json, identity labels, eta=0.')
    graph = f'sameFacesB {k} 4 faces' if cls == 'q1bal' else f'sameFacesQ0B {k} faces'
    s = f'''import Class33Core.Defs
/- {title}
   Generated by class33/py/gen_core.py. Core-Lean pre-validation only, NOT credit. -/
namespace Class33Core.{mod}
open Class33Core

def faces : List (List Nat) := {lst(nl(f) for f in faces)}
def edges : List (List Nat) := {lst(nl(e) for e in edges)}
def muL : List (Nat × Rat) := {nL(T['mu'])}
def kapL : List (List Nat × Rat) := {eL(T['kap'])}
def sideFirstL : List (List Nat × Rat) := {eL(T['sideFirst'])}
def sideSecondL : List (List Nat × Rat) := {eL(T['sideSecond'])}
def faceMaskL : List ((List Nat × Nat) × Rat) := {fm}
def leftFirstL : List (Nat × Rat) := {nL(T['leftFirst'])}
def leftSecondL : List (Nat × Rat) := {nL(T['leftSecond'])}
def rightFirstL : List (Nat × Rat) := {nL(T['rightFirst'])}
def rightSecondL : List (Nat × Rat) := {nL(T['rightSecond'])}

def table : Table where
  faces := faces
  edges := edges
  mu := lookupN muL
  kap := lookupQ kapL
  sideFirst := lookupQ sideFirstL
  sideSecond := lookupQ sideSecondL
  faceMask := fun f s => (faceMaskL.lookup (f,s)).getD 0
  switchMask := fun _ => -1
  leftFirst := lookupN leftFirstL
  leftSecond := lookupN leftSecondL
  rightFirst := lookupN rightFirstL
  rightSecond := lookupN rightSecondL
  width := {q(T['width'])}
  eta := {q(T['eta'])}

/-- The face table is exactly the WIP class face set (recomputed from the transcribed definitions). -/
theorem faces_eq_lean : {graph} = true := by decide +kernel
/-- The edge list is exactly the set of flag edges (= `faceEdges`), 21 edges. -/
theorem edges_ok : table.edgesAreFlagEdgesB = true := by decide +kernel
/-- `CanonicalMaskBalancedQ` (transcribed) holds. -/
theorem balanced : table.balancedB = true := by decide +kernel
/-- `edge_nonnegative` and `eta_nonnegative`. -/
theorem kap_nonneg : table.kapNonnegB = true := by decide +kernel
theorem eta_nonneg : (0 : Rat) ≤ table.eta := by decide +kernel
/-- Exact sharp constant `canonicalSharpConstantUpperQ D kap eta sharpAlpha`. -/
theorem sharp_value : table.sharpConstantUpper sharpAlpha = {q(T['sharp'])} := by decide +kernel

/-- PROPOSED maxima (faces/sectors: historical interval B&B uppers rounded up to 1e-6, NOT Lean-proved;
    switches: {"the nine A25 SwitchBatch bounds (Lean-proved), reindexed j = K-1" if (k == 7 and cls == 'q1bal') else "historical uppers rounded up, NOT Lean-proved"}). -/
def faceMaxP : List Rat := {lst(q(x) for x in faceMax)}
def switchMaxP : List Rat := {lst(q(x) for x in swMax)}
def sectorMaxP : List Rat := {lst(q(x) for x in secMax)}
/-- The strict total would hold with these maxima. -/
theorem strict_with_proposed : table.totalUpper sharpAlpha faceMaxP switchMaxP sectorMaxP < piLo := by decide +kernel
'''
    if k == 7 and cls == 'q1bal':
        s += '\n/-! Bridge: the nine `SharedMomentConcreteSwitchBatch.start0_switchK_*` tuples are the canonical\n    switch coefficients of this table at Lean switch index j = K-1 (mod 9). Values transcribed verbatim. -/\n'
        for K in range(9):
            j = (K - 1) % 9; b = batch[K]
            s += f'theorem batch{K}_is_switch{j} : table.switchP {j} = {q(b["p"])} ∧ table.switchQ {j} = {q(b["q"])} ∧ table.switchB {j} = {q(b["b"])} ∧ table.switchD2 {j} = {q(b["d2"])} ∧ table.switchD1 {j} = {q(b["d1"])} := by decide +kernel\n'
        s += '\n/-- Aggregation: the nine batch bounds, in Lean switch order, sum exactly to `start0_switch_total_bound`. -/\n'
        s += f'theorem switch_aggregate : sumL switchMaxP = (22523/250000 : Rat) := by decide +kernel\n'
        s += f'theorem switchMax_are_batch_bounds : switchMaxP = {lst(q(batch[(j + 1) % 9]["bound"]) for j in range(9))} := by decide +kernel\n'
        # face1: transcribe WIP data verbatim, state canonical slots = data slots reversed
        fsrc = (WIP / 'SharedMomentConcreteFace1Data.lean').read_text()
        def vec(name):
            m = re.search(rf'def {name} : Fin 3 → ℚ := !\[(.*?)\]\n', fsrc).group(1)
            return [F(x.strip()) for x in re.findall(r'\(([^()]*?) : ℚ\)', m)]
        fd = {c: vec(f'start0_face1_{c}') for c in 'pqb'}
        f = [1, 8, 9]
        s += '\n/-- Face {1,8,9}: canonical (sorted-slot) coefficients = SharedMomentConcreteFace1Data start0_face1_{p,q,b} read in slot order 2,1,0. -/\n'
        parts = []
        for c, nm in [('p', 'faceP'), ('q', 'faceQ'), ('b', 'faceB')]:
            parts.append(f'[table.{nm} {nl(f)} 0, table.{nm} {nl(f)} 1, table.{nm} {nl(f)} 2] = [{q(fd[c][2])}, {q(fd[c][1])}, {q(fd[c][0])}]')
        s += 'theorem face189_is_face1_reversed : ' + ' ∧ '.join(parts) + ' := by decide +kernel\n'
    s += f'end Class33Core.{mod}\n'
    wr(OUT / f'{mod}.lean', s)
print('emitted', sorted(p.name for p in OUT.iterdir()))
