import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N11
LABMOD = "import N11Formalization.ActualCanonicalFaceCoordinates\n\n/-! Class33 DRAFT (uncompiled): label lemmas for `canonicalLabel` on 3-element faces, verbatim technique of the\ngreen A25 probe ProbeA25AuditC1804Structure (`decide` does not reduce `orderIsoOfFin`). -/\nset_option autoImplicit false\nnoncomputable section\nnamespace N11Formalization.Class33Labels\nopen ActualCanonicalFaceCoordinates\n\ntheorem lab_zero (f : Finset (Fin 11)) (h : f.card = 3) {i : Fin 11} (hi : i ∈ f)\n    (hmin : ∀ j ∈ f, i ≤ j) : canonicalLabel f h 0 = i := by\n  unfold canonicalLabel\n  have hmem : ((f.orderIsoOfFin h) 0).val ∈ f := ((f.orderIsoOfFin h) 0).property\n  have hle : i ≤ ((f.orderIsoOfFin h) 0).val := hmin _ hmem\n  by_contra hne\n  have hlt : i < ((f.orderIsoOfFin h) 0).val := lt_of_le_of_ne hle (Ne.symm hne)\n  obtain ⟨s, hs⟩ := (f.orderIsoOfFin h).surjective ⟨i, hi⟩\n  have hs0 : (0 : Fin 3) ≤ s := Fin.zero_le s\n  have hge : ((f.orderIsoOfFin h) 0).val ≤ i := by\n    have hm := (f.orderIsoOfFin h).monotone hs0\n    rw [hs] at hm\n    exact hm\n  exact absurd (lt_of_le_of_lt hge hlt) (lt_irrefl _)\n\ntheorem lab_two (f : Finset (Fin 11)) (h : f.card = 3) {i : Fin 11} (hi : i ∈ f)\n    (hmax : ∀ j ∈ f, j ≤ i) : canonicalLabel f h 2 = i := by\n  unfold canonicalLabel\n  have hmem : ((f.orderIsoOfFin h) 2).val ∈ f := ((f.orderIsoOfFin h) 2).property\n  have hle : ((f.orderIsoOfFin h) 2).val ≤ i := hmax _ hmem\n  by_contra hne\n  have hlt : ((f.orderIsoOfFin h) 2).val < i := lt_of_le_of_ne hle hne\n  obtain ⟨s, hs⟩ := (f.orderIsoOfFin h).surjective ⟨i, hi⟩\n  have hs2 : s ≤ (2 : Fin 3) := Fin.le_last s\n  have hge : i ≤ ((f.orderIsoOfFin h) 2).val := by\n    have hm := (f.orderIsoOfFin h).monotone hs2\n    rw [hs] at hm\n    exact hm\n  exact absurd (lt_of_lt_of_le hlt hge) (lt_irrefl _)\n\ntheorem lab_one (f : Finset (Fin 11)) (h : f.card = 3) {a b c : Fin 11}\n    (ha : canonicalLabel f h 0 = a) (hc : canonicalLabel f h 2 = c) (hb : b ∈ f)\n    (hne_a : b ≠ a) (hne_c : b ≠ c) : canonicalLabel f h 1 = b := by\n  unfold canonicalLabel at ha hc ⊢\n  by_contra hne\n  obtain ⟨s, hs⟩ := (f.orderIsoOfFin h).surjective ⟨b, hb⟩\n  have hs' : ((f.orderIsoOfFin h) s).val = b := congrArg Subtype.val hs\n  fin_cases s\n  · simp only [Fin.mk_zero] at hs'\n    rw [ha] at hs'\n    exact hne_a hs'.symm\n  · simp only [Fin.mk_one] at hs'\n    exact hne hs'\n  · simp only [Fin.reduceFinMk] at hs'\n    rw [hc] at hs'\n    exact hne_c hs'.symm\n\nend N11Formalization.Class33Labels\n"
"""Emit the WIP-style (Mathlib, Lean v4.33.1) DRAFT modules for the class line:
  class33/lean/N11Formalization/Class33SwitchBridge.lean   (generic bridge + aggregation, rep7 switches field)
  class33/lean/N11Formalization/Class33RepData.lean        (rep7 / rep1 CanonicalCoeffQ tables, balance)
  class33/lean/N11Formalization/Class33BalancedAssembly.lean (CanonicalCertificate-level balanced consumer,
                                                               rep7 assembly, Face1 permuted face bound)
UNCOMPILED here (no Mathlib in this sandbox). Must be gated by the build line before any credit."""
import json, re, sys, os
from fractions import Fraction as F
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent)); import rep_tables as RT
ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'lean' / 'N11Formalization'; OUT.mkdir(parents=True, exist_ok=True)
WIP = Path(DCP_N11+'/wip/lean/N11Formalization')
def q(x): x = F(x); return f'({x.numerator}/{x.denominator} : ℚ)' if x.denominator != 1 else f'({x.numerator} : ℚ)'
def wr(p, s):
    t = str(p) + '.tmp'; Path(t).write_text(s); os.replace(t, p)
def code(e): return sum(2 ** i for i in e)
src = (WIP / 'SharedMomentConcreteSwitchBatch.lean').read_text()
roots = {int(m.group(1)): m.group(0).split()[-1] for m in re.finditer(r'apply certificate_sound start0_switch(\d)_node_\d+', src)}
roots = {k: v for k, v in roots.items()}

# ---------------- data module ----------------
data = ['import N11Formalization.CanonicalSharedMomentFiniteCertificate', '',
        '/-! Class33 DRAFT (uncompiled): the two q1-balanced representative canonical tables',
        'q1Faces 7 4 (historical start0) and q1Faces 1 4 (historical start2), instantiated from the 9-place',
        'coefficients of shared_moment_dense_certificate_{0,2}_4.json relabelled ring h -> h-1 (mod 9).',
        'Pre-validated: class33/lean-core/Class33Core/Rep{7,1}.lean (core Lean, compiled) and',
        'class33/py/rep_tables.py (Fractions). Data alone gives no class credit. -/',
        'set_option autoImplicit false', 'noncomputable section', 'namespace N11Formalization.Class33RepData',
        'open ActualCanonicalMomentTransport ActualOrderedMetricGraphs ActualCanonicalFaceCoordinates',
        'open ActualSharedMomentRationalCertificate ActualEdgeFlagSums', '',
        '/-- Injective code of a label set (used only to tabulate edge-indexed data). -/',
        'def edgeCode (e : Finset (Fin 11)) : ℕ := ∑ i ∈ e, 2 ^ i.val', '']
for start, k, cls, n, FS, FC in [(0, 7, 'q1bal', 'rep7', 'q1Faces 7 4', 'q1FaceCard 7 4'), (2, 1, 'q1bal', 'rep1', 'q1Faces 1 4', 'q1FaceCard 1 4'), (0, 2, 'q0', 'q0m2', 'q0Faces 2', 'q0FaceCard 2')]:
    T = RT.build(start, k, cls)
    def natmatch(name, d, keys, typ='ℚ'):
        lines = [f'def {name} : ℕ → {typ}']
        for key in keys:
            lines.append(f'  | {key} => {q(d[key]) if typ == "ℚ" else d[key]}')
        lines.append(f'  | _ => 0')
        return '\n'.join(lines)
    data.append(f'/-! ### {n}: {FS} (historical start{start}) -/')
    data.append(natmatch(f'{n}MuN', {i: T['mu'][i] for i in range(11)}, range(11)))
    for fld in ['sideFirst', 'sideSecond', 'kap']:
        d = {code(sorted(e)): v for e, v in T[fld].items()}
        data.append(natmatch(f'{n}{fld[0].upper()+fld[1:]}Code', d, sorted(d)))
    for fld in ['leftFirst', 'leftSecond', 'rightFirst', 'rightSecond']:
        data.append(natmatch(f'{n}{fld[0].upper()+fld[1:]}N', T[fld], range(9)))
    minus = sorted({(code(sorted(f)), code(sorted(RT.flagEdge(f, s)))) for (f, s), v in T['faceMask'].items() if v == -1})
    data.append(f'/-- Face masks: -1 on these (face code, flag-edge code) pairs, +1 otherwise. -/')
    data.append(f'def {n}MinusPairs : List (ℕ × ℕ) := [{",".join(f"({a},{b})" for a, b in minus)}]')
    data.append(f'def {n}MaskCode (fc ec : ℕ) : ℤ := if (fc, ec) ∈ {n}MinusPairs then -1 else 1')
    data.append(f'''def {n}D : CanonicalCoeffQ ({FS}) where
  faceCard := {FC}
  mu := fun i => {n}MuN i.val
  faceMask := fun f s =>
    ({n}MaskCode (edgeCode f.val) (edgeCode (f.val.erase (canonicalLabel f.val ({FC} f) s))) : ℚ)
  switchMask := fun _ => -1
  sideFirst := fun e => {n}SideFirstCode (edgeCode e)
  sideSecond := fun e => {n}SideSecondCode (edgeCode e)
  leftFirst := fun i => {n}LeftFirstN i.val
  leftSecond := fun i => {n}LeftSecondN i.val
  rightFirst := fun i => {n}RightFirstN i.val
  rightSecond := fun i => {n}RightSecondN i.val
  width := {q(T['width'])}
def {n}Kap : Finset (Fin 11) → ℚ := fun e => {n}KapCode (edgeCode e)
def {n}Eta : ℚ := {q(T['eta'])}
''')
data.append('''/-- Slot sums over `canonicalLabel` are sums over the face (orderIsoOfFin is a bijection). This avoids
evaluating `orderIsoOfFin` (which `decide` does not reduce; see A25 LEAD-STATUS C1810/C1812). -/
theorem sum_slots (f : Finset (Fin 11)) (h : f.card=3) (φ : Fin 11 → ℚ) :
    (∑ s : Fin 3, φ (canonicalLabel f h s)) = ∑ i ∈ f, φ i := by
  rw [← Finset.sum_coe_sort f]
  exact Equiv.sum_comp (f.orderIsoOfFin h).toEquiv (fun x : f => φ x.val)
''')
for n, FS, FC in [('rep7', 'q1Faces 7 4', 'q1FaceCard 7 4'), ('rep1', 'q1Faces 1 4', 'q1FaceCard 1 4'), ('q0m2', 'q0Faces 2', 'q0FaceCard 2')]:
    data.append(f'''/-- Decidable form of the balance condition for {n}, over ℤ (masks are ±1). -/
theorem {n}_balance_int : ∀ e ∈ faceEdges ({FS}),
    (∑ f ∈ {FS}, ∑ i ∈ f, (if f.erase i = e then {n}MaskCode (edgeCode f) (edgeCode (f.erase i)) else 0)) +
      (∑ j : Fin 9, if cycleEdge j = e then (-1 : ℤ) else 0) = 0 := by
  decide +kernel

theorem {n}_balance : CanonicalMaskBalancedQ {n}D := by
  intro e he
  have H := {n}_balance_int e he
  unfold canonicalEdgeSumQ switchSumQ
  have hslot : ∀ f : {FS}, (∑ s : Fin 3, if {n}D.flagEdge f s = e then {n}D.faceMask f s else 0) =
      ∑ i ∈ f.val, (if f.val.erase i = e then ({n}MaskCode (edgeCode f.val) (edgeCode (f.val.erase i)) : ℚ) else 0) := by
    intro f
    exact sum_slots f.val ({FC} f)
      (fun i => if f.val.erase i = e then ({n}MaskCode (edgeCode f.val) (edgeCode (f.val.erase i)) : ℚ) else 0)
  simp only [hslot]
  rw [Finset.sum_coe_sort ({FS})
    (fun f => ∑ i ∈ f, (if f.erase i = e then ({n}MaskCode (edgeCode f) (edgeCode (f.erase i)) : ℚ) else 0))]
  have hc := congrArg (fun z : ℤ => (z : ℚ)) H
  push_cast [apply_ite] at hc
  simpa [apply_ite] using hc

theorem {n}_kap_nonneg : ∀ e ∈ faceEdges ({FS}), 0 ≤ {n}Kap e := by
  intro e _
  unfold {n}Kap {n}KapCode
  split <;> norm_num

theorem {n}_eta_nonneg : 0 ≤ {n}Eta := by norm_num [{n}Eta]
''')
data.append('end N11Formalization.Class33RepData')
for n in ['rep7', 'rep1', 'q0m2']:
    data += [f'#print axioms N11Formalization.Class33RepData.{n}_balance', f'#print axioms N11Formalization.Class33RepData.{n}_kap_nonneg']
wr(OUT / 'Class33RepData.lean', '\n'.join(data) + '\n')

# ---------------- switch bridge ----------------
T7 = RT.build(0, 7)
sb = ['import N11Formalization.SharedMomentConcreteSwitchBatch', 'import N11Formalization.Class33RepData', '',
      '''/-! Class33 DRAFT (uncompiled): closes A25 gaps G1/G2 for the nine concrete switch certificates.
* G2 (structure): `switchCertificate_of_direct` turns a direct-leaf tree on `switchCell 0 (1571/1000)`
  into the consumer's `SwitchCertificate` (GradientSwitchLeaf, root containing `switchRoot`).
* G2 (coefficients): batch switch K is canonical switch j = K-1 (mod 9) of `rep7D` (q1Faces 7 4).
  The batch's "start0" is the historical label set; Lean labels are ring h -> h-1, so the index shifts.
* G1 (aggregation): `rep7SwitchMax` uses the PER-SWITCH batch bounds (no uniform 1/2000 or 141/1e6
  qualification is needed or possible: switches K=4,5,8 have bounds 51029/1e6, 4839/2e5, 14023/1e6);
  their sum is exactly `start0_switch_total_bound = 22523/250000`, which enters
  `canonicalTotalUpperQ` additively.
* G4: only `SharedMomentConcreteSwitchBatch.*` names are used, fully qualified; the
  `SharedMomentConcreteLeafControls.start0_switch0_bound = 1/2000` control is never opened. -/''',
      'set_option autoImplicit false', 'noncomputable section', 'namespace N11Formalization.Class33SwitchBridge',
      'open RationalBoxSubdivision SharedMomentFiniteFactorCertificate SharedMomentFactorIntervalCertificate',
      'open ActualSharedMomentAdaptiveCertificate ActualCanonicalMomentTransport ActualEdgeFlagSums Class33RepData',
      'open ActualRingDirectionOrder ActualRingLinkBoundaryData',
      'local notation "SB" => N11Formalization.SharedMomentConcreteSwitchBatch', '',
      '''theorem certificate_mono {I : Type*} [DecidableEq I] {P Q : Cell I → Prop}
    (h : ∀ B, P B → Q B) {B : Cell I} (T : Certificate P B) : Certificate Q B := by
  induction T with
  | accept hp => exact Certificate.accept (h _ hp)
  | split i t hlo hhi _ _ ihl ihr => exact Certificate.split i t hlo hhi ihl ihr

theorem fullSwitchCell_contains :
    ContainsCell (SharedMomentConcreteLeafControls.switchCell 0 (1571/1000 : ℚ)) switchRoot := by
  intro i
  fin_cases i
  refine ⟨by simp [SharedMomentConcreteLeafControls.switchCell,switchRoot],?_⟩
  simp only [SharedMomentConcreteLeafControls.switchCell,switchRoot]
  norm_num [RatInterval.piHi]

/-- Structure bridge: a direct-leaf tree over the full switch cell is a consumer `SwitchCertificate`. -/
def switchCertificate_of_direct {p q b d2 d1 M : ℚ}
    (T : Certificate (fun B => switchDirectUpperQ p q b d2 d1 B ≤ M)
      (SharedMomentConcreteLeafControls.switchCell 0 (1571/1000 : ℚ))) :
    SwitchCertificate p q b d2 d1 M where
  root := SharedMomentConcreteLeafControls.switchCell 0 (1571/1000 : ℚ)
  contains := fullSwitchCell_contains
  tree := certificate_mono (fun _ h => Or.inl (Or.inr (Or.inl h))) T
''']
for K in range(9):
    sb.append(f'''def batchSwitch{K} : SwitchCertificate SB.start0_switch{K}_p SB.start0_switch{K}_q SB.start0_switch{K}_b
    SB.start0_switch{K}_d2 SB.start0_switch{K}_d1 SB.start0_switch{K}_bound :=
  switchCertificate_of_direct SB.{roots[K]}''')
sb.append('''
/-- Per-switch maxima in Lean switch order j (batch switch K = j+1 mod 9). -/
def rep7SwitchMaxN : ℕ → ℚ''')
for j in range(9):
    sb.append(f'  | {j} => SB.start0_switch{(j + 1) % 9}_bound')
sb.append('  | _ => 0')
sb.append('def rep7SwitchMax (i : Fin 9) : ℚ := rep7SwitchMaxN i.val')
sb.append('''
/-- G1: aggregation. The nine per-switch bounds sum exactly to `start0_switch_total_bound`. -/
theorem rep7_switch_aggregate :
    (∑ i : Fin 9, rep7SwitchMax i) = SB.start0_switch_total_bound := by
  rw [Fin.sum_univ_eq_sum_range (fun n => rep7SwitchMaxN n) 9]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,rep7SwitchMaxN]
  norm_num [SB.start0_switch0_bound,SB.start0_switch1_bound,SB.start0_switch2_bound,SB.start0_switch3_bound,
    SB.start0_switch4_bound,SB.start0_switch5_bound,SB.start0_switch6_bound,SB.start0_switch7_bound,
    SB.start0_switch8_bound,SB.start0_switch_total_bound]
''')
for j in range(9):
    K = (j + 1) % 9
    e = sorted([j, (j + 1) % 9]); c = code(e)
    names = ','.join(f'SB.start0_switch{K}_{x}' for x in ['p', 'q', 'b', 'd2', 'd1'])
    sb.append(f'''/-- G2 coefficient identity: canonical switch {j} of rep7 = batch switch {K}. -/
theorem rep7_switch{j}_eq :
    canonicalSwitchP rep7D rep7Kap {j}=SB.start0_switch{K}_p ∧ canonicalSwitchQ rep7D {j}=SB.start0_switch{K}_q ∧
    canonicalSwitchB rep7D {j}=SB.start0_switch{K}_b ∧ canonicalSwitchD2 rep7D {j}=SB.start0_switch{K}_d2 ∧
    canonicalSwitchD1 rep7D {j}=SB.start0_switch{K}_d1 := by
  have hc : cycleEdge {j} = ({{({j} : Fin 11),({(j + 1) % 9} : Fin 11)}} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({{({j} : Fin 11),({(j + 1) % 9} : Fin 11)}} : Finset (Fin 11)) = {c} := by decide
  have hpred : ((({j} : Fin 9) - 1 : Fin 9) : ℕ) = {(j - 1) % 9} := by decide
  have hj : (({j} : Fin 9) : ℕ) = {j} := rfl
  have hne : ({j} : Fin 11) ≠ ({(j + 1) % 9} : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      rep7D,rep7Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [rep7MuN,rep7SideFirstCode,rep7SideSecondCode,rep7KapCode,rep7LeftFirstN,rep7LeftSecondN,
      rep7RightFirstN,rep7RightSecondN,{names}]
''')
sb.append('''/-- The `switches` field of a `FiniteCanonicalCertificate rep7D rep7Kap 0 rep7Eta sharpAlpha`. -/
def rep7Switches : ∀ i : Fin 9, SwitchCertificate (canonicalSwitchP rep7D rep7Kap i)
    (canonicalSwitchQ rep7D i) (canonicalSwitchB rep7D i) (canonicalSwitchD2 rep7D i)
    (canonicalSwitchD1 rep7D i) (rep7SwitchMax i) := by
  intro i
  fin_cases i''')
for j in range(9):
    K = (j + 1) % 9
    sb.append(f'''  · obtain ⟨h1,h2,h3,h4,h5⟩ := rep7_switch{j}_eq
    have hm : rep7SwitchMax ({j} : Fin 9) = SB.start0_switch{K}_bound := rfl
    simp only [Fin.isValue] at h1 h2 h3 h4 h5 ⊢
    rw [h1,h2,h3,h4,h5,hm]
    exact batchSwitch{K}''')
sb.append('end N11Formalization.Class33SwitchBridge')
sb += ['#print axioms N11Formalization.Class33SwitchBridge.certificate_mono',
       '#print axioms N11Formalization.Class33SwitchBridge.switchCertificate_of_direct',
       '#print axioms N11Formalization.Class33SwitchBridge.rep7_switch_aggregate',
       '#print axioms N11Formalization.Class33SwitchBridge.rep7Switches'] + \
      [f'#print axioms N11Formalization.Class33SwitchBridge.rep7_switch{j}_eq' for j in range(9)]
wr(OUT / 'Class33SwitchBridge.lean', '\n'.join(sb) + '\n')

# ---------------- assembly ----------------
asm = '''import N11Formalization.Class33SwitchBridge
import N11Formalization.CanonicalBalancedFiniteClassCertificate
import N11Formalization.SharedMomentConcreteFace1Certificate
import N11Formalization.Class33Labels

/-! Class33 DRAFT (uncompiled). What remains for the q1-balanced class, made exact:
* `balanced_exclusion_of_two_canonical` = `balanced_exclusion_of_two_finite` but consuming
  `CanonicalCertificate`s (semantic bounds), so face bounds may come from ANY sound theorem, e.g. a
  slot-permuted tree (`face_upper_of_permuted_coefficients`).
* `rep7_certificate`: for cut 7, given the 11 face bounds and 9 sector bounds and the strict total,
  produce the `CanonicalCertificate`; balance, kap/eta signs, the sharp bracket and ALL NINE SWITCH
  bounds are supplied (switches from the A25 SwitchBatch via Class33SwitchBridge).
* `rep7_face189_upper`: the A25 Face1 tree (`start0_face1_full_domain_upper`, proved) IS the face
  {1,8,9} bound of rep7 after reversing slots (canonical slot s = data slot 2-s).
No class credit until the remaining 10+9 (rep7) and 11+9+9 (rep1) factor bounds are proved. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.Class33BalancedAssembly
open CanonicalSharedMomentFiniteCertificate CanonicalSharedMomentOrbitTransport CanonicalBalancedFiniteClassCertificate
open ActualCanonicalSharedMomentConsumer ActualCanonicalMomentTransport ActualOrderedMetricGraphs
open ActualMetricClassReduction ActualBoundaryNineTies SharedMomentFactorGridCertificate
open SharedMomentFiniteFactorCertificate Class33RepData Class33SwitchBridge Class33Labels

theorem balanced_exclusion_of_two_canonical
    (H7 : ∃ D : CanonicalCoeffQ (q1Faces 7 4), ∃ kap : Finset (Fin 11) → ℚ, ∃ eta : ℚ,
      Nonempty (CanonicalCertificate D kap 0 eta sharpAlpha))
    (H1 : ∃ D : CanonicalCoeffQ (q1Faces 1 4), ∃ kap : Finset (Fin 11) → ℚ, ∃ eta : ℚ,
      Nonempty (CanonicalCertificate D kap 0 eta sharpAlpha)) : Q1RunExclusion 4 := by
  have Hall := balanced_certificates_of_two sharpAlpha H7 H1
  intro c r h hr R O hm
  obtain ⟨v⟩ := nineTies_of_cover h.cover hr h.labels h.midpoint_order
  have he : O.run_length=(4 : Fin 8) := Fin.ext hm
  have hcut := Hall O.cut
  rw [← he] at hcut
  obtain ⟨D,kap,eta,⟨K⟩⟩ := hcut
  exact exclude_q1_ordered h hr R v O D kap eta sharpAlpha K

/-- rep7 certificate from the remaining face/sector bounds. -/
def rep7_certificate (faceMax : q1Faces 7 4 → ℚ) (sectorMax : Fin 9 → ℚ)
    (hface : ∀ (f : q1Faces 7 4) (a : Fin 3 → ℝ),
      (∀ s, a s ∈ Set.Icc (0 : ℝ) Real.pi) → (∑ s : Fin 3, a s)=Real.pi →
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        faceObjective (fun s => (canonicalFaceP rep7D rep7Kap f s : ℝ))
          (fun s => (canonicalFaceQ rep7D f s : ℝ)) (fun s => (canonicalFaceB rep7D f s : ℝ)) a y ≤ faceMax f)
    (hsector : ∀ i : Fin 9, EfficientSectorCertificate (canonicalSectorC rep7D 0 rep7Eta i)
      (rep7D.mu (nextSite i)) (rep7D.leftSecond i) (rep7D.rightSecond i)
      (rep7D.leftFirst i) (rep7D.rightFirst i) (sectorMax i))
    (hstrict : canonicalTotalUpperQ rep7D rep7Kap rep7Eta sharpAlpha faceMax rep7SwitchMax sectorMax <
      RatInterval.piLo) :
    CanonicalCertificate rep7D rep7Kap 0 rep7Eta sharpAlpha where
  faceMax := faceMax
  switchMax := rep7SwitchMax
  sectorMax := sectorMax
  balance := rep7_balance
  edge_nonnegative := rep7_kap_nonneg
  eta_nonnegative := rep7_eta_nonneg
  bracket := sharpAlpha_bracket
  bounds := ⟨hface,fun i => (rep7Switches i).sound,fun i => (hsector i).sound⟩
  strict := hstrict

/-- The face {1,8,9} of rep7 is bounded by the proved A25 Face1 tree, slots reversed
(canonical slot s carries label (1,8,9)_s; Face1 data slots carry (9,8,1)). -/
theorem rep7_face189_upper (hmem : ({1,8,9} : Finset (Fin 11)) ∈ q1Faces 7 4) :
    ∀ a : Fin 3 → ℝ, (∀ s, a s ∈ Set.Icc (0 : ℝ) Real.pi) → (∑ s : Fin 3, a s)=Real.pi →
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        faceObjective (fun s => (canonicalFaceP rep7D rep7Kap ⟨_,hmem⟩ s : ℝ))
          (fun s => (canonicalFaceQ rep7D ⟨_,hmem⟩ s : ℝ)) (fun s => (canonicalFaceB rep7D ⟨_,hmem⟩ s : ℝ)) a y ≤
          (SharedMomentConcreteFace1.start0_face1_bound : ℝ) := by
  have h3 := q1FaceCard 7 4 ⟨({1,8,9} : Finset (Fin 11)), hmem⟩
  have l0 : canonicalLabel ({1,8,9} : Finset (Fin 11)) h3 0 = 1 := lab_zero _ _ (by decide) (by decide)
  have l2 : canonicalLabel ({1,8,9} : Finset (Fin 11)) h3 2 = 9 := lab_two _ _ (by decide) (by decide)
  have l1 : canonicalLabel ({1,8,9} : Finset (Fin 11)) h3 1 = 8 :=
    lab_one _ _ l0 l2 (by decide) (by decide) (by decide)
  have e0 : edgeCode (({1,8,9} : Finset (Fin 11)).erase 1) = 768 := by decide
  have e1 : edgeCode (({1,8,9} : Finset (Fin 11)).erase 8) = 514 := by decide
  have e2 : edgeCode (({1,8,9} : Finset (Fin 11)).erase 9) = 258 := by decide
  have c3 : edgeCode ({1,8,9} : Finset (Fin 11)) = 770 := by decide
  have r0 : Fin.rev (0 : Fin 3) = 2 := by decide
  have r1 : Fin.rev (1 : Fin 3) = 1 := by decide
  have r2 : Fin.rev (2 : Fin 3) = 0 := by decide
  have hp : ∀ s : Fin 3, canonicalFaceP rep7D rep7Kap ⟨_,hmem⟩ s =
      SharedMomentConcreteFace1.start0_face1_p (Fin.rev s) := by
    intro s
    fin_cases s <;>
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,rep7Kap,
        l0,l1,l2,e0,e1,e2,r0,r1,r2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MuN,rep7KapCode,SharedMomentConcreteFace1.start0_face1_p]
  have hq : ∀ s : Fin 3, canonicalFaceQ rep7D ⟨_,hmem⟩ s =
      SharedMomentConcreteFace1.start0_face1_q (Fin.rev s) := by
    intro s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,r0,r1,r2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideSecondCode,SharedMomentConcreteFace1.start0_face1_q]
  have hb : ∀ s : Fin 3, canonicalFaceB rep7D ⟨_,hmem⟩ s =
      SharedMomentConcreteFace1.start0_face1_b (Fin.rev s) := by
    intro s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,r0,r1,r2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideFirstCode,SharedMomentConcreteFace1.start0_face1_b]
  have H := SharedMomentFactorPermutation.face_upper_of_permuted_coefficients
    (fun s => (SharedMomentConcreteFace1.start0_face1_p s : ℝ))
    (fun s => (SharedMomentConcreteFace1.start0_face1_q s : ℝ))
    (fun s => (SharedMomentConcreteFace1.start0_face1_b s : ℝ)) _ Fin.revPerm
    SharedMomentConcreteFace1.start0_face1_full_domain_upper
  intro a ha hsum y hy
  have hh := H a ha hsum y hy
  simp only [Fin.revPerm_apply] at hh
  simpa only [hp,hq,hb] using hh

end N11Formalization.Class33BalancedAssembly
#print axioms N11Formalization.Class33BalancedAssembly.balanced_exclusion_of_two_canonical
#print axioms N11Formalization.Class33BalancedAssembly.rep7_certificate
#print axioms N11Formalization.Class33BalancedAssembly.rep7_face189_upper
'''
wr(OUT / 'Class33BalancedAssembly.lean', asm)
wr(OUT / 'Class33Labels.lean', LABMOD)
print('emitted', sorted(p.name for p in OUT.iterdir()))
