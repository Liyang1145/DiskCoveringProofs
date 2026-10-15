import N11Formalization.C450AngularCellMajorant
import N11Formalization.C450FourthRadialC01
import N11Formalization.C450FourthRadialC02
import N11Formalization.C450FourthRadialC03
import N11Formalization.C450FourthRadialC04
import N11Formalization.C450FourthRadialC05
import N11Formalization.C450FourthRadialC06
import N11Formalization.C450FourthRadialC07
import N11Formalization.C450FourthRadialC08
import N11Formalization.C450ThirdSegment

/-! Actual FOURTH normalized C450 source segment, complete eight direction
cells and closed radial continuum. Remaining32 stay explicit. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450FourthSegment
open C450RadialPacketKernel C450AngularCellMajorant C450AngularMajorant
open C450NormalizedInterface

abbrev Case := Fin 8
def fourth : TenSeg := c450Segs[3]'(by decide +kernel)
theorem fourth_mem : fourth ∈ c450Segs := by decide +kernel
theorem nn0 : |fourth.a1|+|fourth.a2|+|fourth.a3| ≤ fourth.a0 :=
  (c450Segs_nonneg fourth fourth_mem).1
theorem nn1 : |fourth.b1|+|fourth.b2|+|fourth.b3| ≤ fourth.b0 :=
  (c450Segs_nonneg fourth fourth_mem).2
def W0 : TrigDensity := fourth.W0 nn0
def W1 : TrigDensity := fourth.W1 nn1
def cells : Case → Cell :=
  ![⟨-1,-3/4⟩,⟨-3/4,-1/2⟩,⟨-1/2,-1/4⟩,⟨-1/4,0⟩,
    ⟨0,1/4⟩,⟨1/4,1/2⟩,⟨1/2,3/4⟩,⟨3/4,1⟩]
def params : Case → Params :=
  ![C450FourthRadialC01.params,C450FourthRadialC02.params,
    C450FourthRadialC03.params,C450FourthRadialC04.params,
    C450FourthRadialC05.params,C450FourthRadialC06.params,
    C450FourthRadialC07.params,C450FourthRadialC08.params]

theorem cells_valid (i : Case) : ValidCell (cells i) := by
  fin_cases i <;> constructor <;> norm_num [cells]

theorem cells_cover : CoversDirections cells := by
  let P : ℝ → Prop := fun q => ∃ i : Case, q ∈ Set.Icc (cells i).lo (cells i).hi
  have h0 : ∀ q ∈ Set.Icc (-1:ℝ) (-3/4), P q := by
    intro q h
    exact ⟨0,by simpa [cells] using h⟩
  have h1 : ∀ q ∈ Set.Icc (-3/4:ℝ) (-1/2), P q := by
    intro q h
    exact ⟨1,by simpa [cells] using h⟩
  have h2 : ∀ q ∈ Set.Icc (-1/2:ℝ) (-1/4), P q := by
    intro q h
    exact ⟨2,by simpa [cells] using h⟩
  have h3 : ∀ q ∈ Set.Icc (-1/4:ℝ) 0, P q := by
    intro q h
    exact ⟨3,by simpa [cells] using h⟩
  have h4 : ∀ q ∈ Set.Icc (0:ℝ) (1/4), P q := by
    intro q h
    exact ⟨4,by simpa [cells] using h⟩
  have h5 : ∀ q ∈ Set.Icc (1/4:ℝ) (1/2), P q := by
    intro q h
    exact ⟨5,by simpa [cells] using h⟩
  have h6 : ∀ q ∈ Set.Icc (1/2:ℝ) (3/4), P q := by
    intro q h
    exact ⟨6,by simpa [cells] using h⟩
  have h7 : ∀ q ∈ Set.Icc (3/4:ℝ) 1, P q := by
    intro q h
    exact ⟨7,by simpa [cells] using h⟩
  exact C450FirstRadialKernel.interval_join
    (C450FirstRadialKernel.interval_join
      (C450FirstRadialKernel.interval_join h0 h1)
      (C450FirstRadialKernel.interval_join h2 h3))
    (C450FirstRadialKernel.interval_join
      (C450FirstRadialKernel.interval_join h4 h5)
      (C450FirstRadialKernel.interval_join h6 h7))

theorem params_valid (i : Case) : ValidParams (params i) := by
  fin_cases i
  · exact C450FourthRadialC01.params_valid
  · exact C450FourthRadialC02.params_valid
  · exact C450FourthRadialC03.params_valid
  · exact C450FourthRadialC04.params_valid
  · exact C450FourthRadialC05.params_valid
  · exact C450FourthRadialC06.params_valid
  · exact C450FourthRadialC07.params_valid
  · exact C450FourthRadialC08.params_valid

theorem params_A (i : Case) : (params i).A = fourth.a0 := by
  fin_cases i <;> rfl
theorem params_B (i : Case) : (params i).B = fourth.b0 := by
  fin_cases i <;> rfl

theorem model_bound (i : Case) :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50), model (params i) r < (cap (params i):ℝ) := by
  fin_cases i
  · exact C450FourthRadialC01.bound
  · exact C450FourthRadialC02.bound
  · exact C450FourthRadialC03.bound
  · exact C450FourthRadialC04.bound
  · exact C450FourthRadialC05.bound
  · exact C450FourthRadialC06.bound
  · exact C450FourthRadialC07.bound
  · exact C450FourthRadialC08.bound

theorem model_eq0 (r : ℝ) : model (params 0) r =
    angularModel W0.a0 (coefficient W1 (cells 0)) (offset (1/125) (3/250) (cells 0)) r := by
  change model C450FourthRadialC01.params r =
    angularModel W0.a0 (coefficient W1 ⟨-1,-3/4⟩) (offset (1/125) (3/250) ⟨-1,-3/4⟩) r
  norm_num [model,params,cells,C450FourthRadialC01.params,coefficient,offset,tailSup,
    W0,W1,fourth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq1 (r : ℝ) : model (params 1) r =
    angularModel W0.a0 (coefficient W1 (cells 1)) (offset (1/125) (3/250) (cells 1)) r := by
  change model C450FourthRadialC02.params r =
    angularModel W0.a0 (coefficient W1 ⟨-3/4,-1/2⟩) (offset (1/125) (3/250) ⟨-3/4,-1/2⟩) r
  norm_num [model,params,cells,C450FourthRadialC02.params,coefficient,offset,tailSup,
    W0,W1,fourth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq2 (r : ℝ) : model (params 2) r =
    angularModel W0.a0 (coefficient W1 (cells 2)) (offset (1/125) (3/250) (cells 2)) r := by
  change model C450FourthRadialC03.params r =
    angularModel W0.a0 (coefficient W1 ⟨-1/2,-1/4⟩) (offset (1/125) (3/250) ⟨-1/2,-1/4⟩) r
  norm_num [model,params,cells,C450FourthRadialC03.params,coefficient,offset,tailSup,
    W0,W1,fourth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq3 (r : ℝ) : model (params 3) r =
    angularModel W0.a0 (coefficient W1 (cells 3)) (offset (1/125) (3/250) (cells 3)) r := by
  change model C450FourthRadialC04.params r =
    angularModel W0.a0 (coefficient W1 ⟨-1/4,0⟩) (offset (1/125) (3/250) ⟨-1/4,0⟩) r
  norm_num [model,params,cells,C450FourthRadialC04.params,coefficient,offset,tailSup,
    W0,W1,fourth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq4 (r : ℝ) : model (params 4) r =
    angularModel W0.a0 (coefficient W1 (cells 4)) (offset (1/125) (3/250) (cells 4)) r := by
  change model C450FourthRadialC05.params r =
    angularModel W0.a0 (coefficient W1 ⟨0,1/4⟩) (offset (1/125) (3/250) ⟨0,1/4⟩) r
  norm_num [model,params,cells,C450FourthRadialC05.params,coefficient,offset,tailSup,
    W0,W1,fourth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq5 (r : ℝ) : model (params 5) r =
    angularModel W0.a0 (coefficient W1 (cells 5)) (offset (1/125) (3/250) (cells 5)) r := by
  change model C450FourthRadialC06.params r =
    angularModel W0.a0 (coefficient W1 ⟨1/4,1/2⟩) (offset (1/125) (3/250) ⟨1/4,1/2⟩) r
  norm_num [model,params,cells,C450FourthRadialC06.params,coefficient,offset,tailSup,
    W0,W1,fourth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq6 (r : ℝ) : model (params 6) r =
    angularModel W0.a0 (coefficient W1 (cells 6)) (offset (1/125) (3/250) (cells 6)) r := by
  change model C450FourthRadialC07.params r =
    angularModel W0.a0 (coefficient W1 ⟨1/2,3/4⟩) (offset (1/125) (3/250) ⟨1/2,3/4⟩) r
  norm_num [model,params,cells,C450FourthRadialC07.params,coefficient,offset,tailSup,
    W0,W1,fourth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq7 (r : ℝ) : model (params 7) r =
    angularModel W0.a0 (coefficient W1 (cells 7)) (offset (1/125) (3/250) (cells 7)) r := by
  change model C450FourthRadialC08.params r =
    angularModel W0.a0 (coefficient W1 ⟨3/4,1⟩) (offset (1/125) (3/250) ⟨3/4,1⟩) r
  norm_num [model,params,cells,C450FourthRadialC08.params,coefficient,offset,tailSup,
    W0,W1,fourth,c450Segs,TenSeg.W0,TenSeg.W1]

theorem model_eq (i : Case) (r : ℝ) : model (params i) r =
    angularModel W0.a0 (coefficient W1 (cells i)) (offset (1/125) (3/250) (cells i)) r := by
  fin_cases i
  · exact model_eq0 r
  · exact model_eq1 r
  · exact model_eq2 r
  · exact model_eq3 r
  · exact model_eq4 r
  · exact model_eq5 r
  · exact model_eq6 r
  · exact model_eq7 r

theorem radial_paid (i : Case) : CellRadialBound W0 W1 (1/125) (3/250) (cells i) := by
  intro r hr0 hr1
  have hb := model_bound i r ⟨hr0,hr1⟩
  rw [model_eq] at hb
  have hc := cap_lt_actual (params i) (params_valid i)
  have ha : ((params i).A:ℝ) = W0.a0 := by
    change ((params i).A:ℝ) = (fourth.a0:ℝ)
    exact congrArg (fun x : ℚ => (x:ℝ)) (params_A i)
  have hbb : ((params i).B:ℝ) = W1.a0 := by
    change ((params i).B:ℝ) = (fourth.b0:ℝ)
    exact congrArg (fun x : ℚ => (x:ℝ)) (params_B i)
  rw [ha,hbb] at hc
  exact hb.trans hc

theorem fourth_paid : SegmentNormalized fourth := by
  intro h0 h1
  have hp := normalized_of_cells cells cells_valid cells_cover W0 W1
    (by norm_num [W0,fourth,c450Segs,TenSeg.W0])
    (by norm_num [W0,fourth,c450Segs,TenSeg.W0])
    (by norm_num [W0,fourth,c450Segs,TenSeg.W0])
    (by norm_num [W1,fourth,c450Segs,TenSeg.W1])
    (1/125) (3/250) (by norm_num) (by norm_num) radial_paid
  have he0 : (fourth.eLo:ℝ) = (1/125:ℝ) := by norm_num [fourth,c450Segs]
  have he1 : (fourth.eHi:ℝ) = (3/250:ℝ) := by norm_num [fourth,c450Segs]
  rw [he0,he1]
  exact hp

def remainingSegs : List TenSeg := c450Segs.drop 4
theorem remaining_count : remainingSegs.length = 32 := by decide +kernel
theorem third_remaining_split : C450ThirdSegment.remainingSegs = fourth :: remainingSegs := rfl
def RemainingSourceObligation : Prop := ∀ s ∈ remainingSegs, SegmentNormalized s
theorem third_remaining_of_remaining (hr : RemainingSourceObligation) :
    C450ThirdSegment.RemainingSourceObligation := by
  intro s hs
  rw [third_remaining_split] at hs
  simp only [List.mem_cons] at hs
  rcases hs with hfourth | hrest
  · rw [hfourth]
    exact fourth_paid
  · exact hr s hrest
theorem source_of_remaining (hr : RemainingSourceObligation) : SourceObligation :=
  C450ThirdSegment.source_of_remaining (third_remaining_of_remaining hr)
theorem atom_of_remaining (hr : RemainingSourceObligation) : C450Atom :=
  atom_of_source (source_of_remaining hr)
end N11Formalization.C450FourthSegment
#check @N11Formalization.C450FourthSegment.fourth_paid
#check @N11Formalization.C450FourthSegment.atom_of_remaining
#print axioms N11Formalization.C450FourthSegment.cells_cover
#print axioms N11Formalization.C450FourthSegment.radial_paid
#print axioms N11Formalization.C450FourthSegment.fourth_paid
#print axioms N11Formalization.C450FourthSegment.atom_of_remaining
