import N11Formalization.C450AngularCellMajorant
import N11Formalization.C450FifthRadialC01
import N11Formalization.C450FifthRadialC02
import N11Formalization.C450FifthRadialC03
import N11Formalization.C450FifthRadialC04
import N11Formalization.C450FifthRadialC05
import N11Formalization.C450FifthRadialC06
import N11Formalization.C450FifthRadialC07
import N11Formalization.C450FifthRadialC08
import N11Formalization.C450FifthRadialC09
import N11Formalization.C450FifthRadialC10
import N11Formalization.C450FifthRadialC11
import N11Formalization.C450FifthRadialC12
import N11Formalization.C450FifthRadialC13
import N11Formalization.C450FifthRadialC14
import N11Formalization.C450FifthRadialC15
import N11Formalization.C450FifthRadialC16
import N11Formalization.C450FourthSegment
/-! Actual FIFTH normalized C450 source segment; all other31 remain explicit.
Closed16-cell cq coverage and403 exact closed radial packets. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450FifthSegment
open C450RadialPacketKernel C450AngularCellMajorant C450AngularMajorant
open C450NormalizedInterface
abbrev Case := Fin 16
def fifth : TenSeg := c450Segs[4]'(by decide +kernel)
theorem fifth_mem : fifth ∈ c450Segs := by decide +kernel
theorem nn0 : |fifth.a1|+|fifth.a2|+|fifth.a3| ≤ fifth.a0 :=
  (c450Segs_nonneg fifth fifth_mem).1
theorem nn1 : |fifth.b1|+|fifth.b2|+|fifth.b3| ≤ fifth.b0 :=
  (c450Segs_nonneg fifth fifth_mem).2
def W0 : TrigDensity := fifth.W0 nn0
def W1 : TrigDensity := fifth.W1 nn1
def cells : Case → Cell := ![⟨-1,(-7/8)⟩,⟨(-7/8),(-3/4)⟩,⟨(-3/4),(-5/8)⟩,⟨(-5/8),(-1/2)⟩,⟨(-1/2),(-3/8)⟩,⟨(-3/8),(-1/4)⟩,⟨(-1/4),(-1/8)⟩,⟨(-1/8),0⟩,⟨0,(1/8)⟩,⟨(1/8),(1/4)⟩,⟨(1/4),(3/8)⟩,⟨(3/8),(1/2)⟩,⟨(1/2),(5/8)⟩,⟨(5/8),(3/4)⟩,⟨(3/4),(7/8)⟩,⟨(7/8),1⟩]
def params : Case → Params := ![C450FifthRadialC01.params,C450FifthRadialC02.params,C450FifthRadialC03.params,C450FifthRadialC04.params,C450FifthRadialC05.params,C450FifthRadialC06.params,C450FifthRadialC07.params,C450FifthRadialC08.params,C450FifthRadialC09.params,C450FifthRadialC10.params,C450FifthRadialC11.params,C450FifthRadialC12.params,C450FifthRadialC13.params,C450FifthRadialC14.params,C450FifthRadialC15.params,C450FifthRadialC16.params]
theorem cells_valid (i : Case) : ValidCell (cells i) := by
  fin_cases i <;> constructor <;> norm_num [cells]
theorem cells_cover : CoversDirections cells := by
  let P : ℝ → Prop := fun q => ∃ i : Case, q ∈ Set.Icc (cells i).lo (cells i).hi
  have h0 : ∀ q ∈ Set.Icc (-1:ℝ) ((-7:ℝ)/8), P q := by
    intro q h
    exact ⟨0,by simpa [cells] using h⟩
  have h1 : ∀ q ∈ Set.Icc ((-7:ℝ)/8) ((-3:ℝ)/4), P q := by
    intro q h
    exact ⟨1,by simpa [cells] using h⟩
  have h2 : ∀ q ∈ Set.Icc ((-3:ℝ)/4) ((-5:ℝ)/8), P q := by
    intro q h
    exact ⟨2,by simpa [cells] using h⟩
  have h3 : ∀ q ∈ Set.Icc ((-5:ℝ)/8) ((-1:ℝ)/2), P q := by
    intro q h
    exact ⟨3,by simpa [cells] using h⟩
  have h4 : ∀ q ∈ Set.Icc ((-1:ℝ)/2) ((-3:ℝ)/8), P q := by
    intro q h
    exact ⟨4,by simpa [cells] using h⟩
  have h5 : ∀ q ∈ Set.Icc ((-3:ℝ)/8) ((-1:ℝ)/4), P q := by
    intro q h
    exact ⟨5,by simpa [cells] using h⟩
  have h6 : ∀ q ∈ Set.Icc ((-1:ℝ)/4) ((-1:ℝ)/8), P q := by
    intro q h
    exact ⟨6,by simpa [cells] using h⟩
  have h7 : ∀ q ∈ Set.Icc ((-1:ℝ)/8) (0:ℝ), P q := by
    intro q h
    exact ⟨7,by simpa [cells] using h⟩
  have h8 : ∀ q ∈ Set.Icc (0:ℝ) ((1:ℝ)/8), P q := by
    intro q h
    exact ⟨8,by simpa [cells] using h⟩
  have h9 : ∀ q ∈ Set.Icc ((1:ℝ)/8) ((1:ℝ)/4), P q := by
    intro q h
    exact ⟨9,by simpa [cells] using h⟩
  have h10 : ∀ q ∈ Set.Icc ((1:ℝ)/4) ((3:ℝ)/8), P q := by
    intro q h
    exact ⟨10,by simpa [cells] using h⟩
  have h11 : ∀ q ∈ Set.Icc ((3:ℝ)/8) ((1:ℝ)/2), P q := by
    intro q h
    exact ⟨11,by simpa [cells] using h⟩
  have h12 : ∀ q ∈ Set.Icc ((1:ℝ)/2) ((5:ℝ)/8), P q := by
    intro q h
    exact ⟨12,by simpa [cells] using h⟩
  have h13 : ∀ q ∈ Set.Icc ((5:ℝ)/8) ((3:ℝ)/4), P q := by
    intro q h
    exact ⟨13,by simpa [cells] using h⟩
  have h14 : ∀ q ∈ Set.Icc ((3:ℝ)/4) ((7:ℝ)/8), P q := by
    intro q h
    exact ⟨14,by simpa [cells] using h⟩
  have h15 : ∀ q ∈ Set.Icc ((7:ℝ)/8) (1:ℝ), P q := by
    intro q h
    exact ⟨15,by simpa [cells] using h⟩
  exact (C450FirstRadialKernel.interval_join (C450FirstRadialKernel.interval_join (C450FirstRadialKernel.interval_join (C450FirstRadialKernel.interval_join h0 h1) (C450FirstRadialKernel.interval_join h2 h3)) (C450FirstRadialKernel.interval_join (C450FirstRadialKernel.interval_join h4 h5) (C450FirstRadialKernel.interval_join h6 h7))) (C450FirstRadialKernel.interval_join (C450FirstRadialKernel.interval_join (C450FirstRadialKernel.interval_join h8 h9) (C450FirstRadialKernel.interval_join h10 h11)) (C450FirstRadialKernel.interval_join (C450FirstRadialKernel.interval_join h12 h13) (C450FirstRadialKernel.interval_join h14 h15))))
theorem params_valid (i : Case) : ValidParams (params i) := by
  fin_cases i
  · exact C450FifthRadialC01.params_valid
  · exact C450FifthRadialC02.params_valid
  · exact C450FifthRadialC03.params_valid
  · exact C450FifthRadialC04.params_valid
  · exact C450FifthRadialC05.params_valid
  · exact C450FifthRadialC06.params_valid
  · exact C450FifthRadialC07.params_valid
  · exact C450FifthRadialC08.params_valid
  · exact C450FifthRadialC09.params_valid
  · exact C450FifthRadialC10.params_valid
  · exact C450FifthRadialC11.params_valid
  · exact C450FifthRadialC12.params_valid
  · exact C450FifthRadialC13.params_valid
  · exact C450FifthRadialC14.params_valid
  · exact C450FifthRadialC15.params_valid
  · exact C450FifthRadialC16.params_valid
theorem params_A (i : Case) : (params i).A = fifth.a0 := by
  fin_cases i <;> rfl
theorem params_B (i : Case) : (params i).B = fifth.b0 := by
  fin_cases i <;> rfl
theorem model_bound (i : Case) :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50), model (params i) r < (cap (params i):ℝ) := by
  fin_cases i
  · exact C450FifthRadialC01.bound
  · exact C450FifthRadialC02.bound
  · exact C450FifthRadialC03.bound
  · exact C450FifthRadialC04.bound
  · exact C450FifthRadialC05.bound
  · exact C450FifthRadialC06.bound
  · exact C450FifthRadialC07.bound
  · exact C450FifthRadialC08.bound
  · exact C450FifthRadialC09.bound
  · exact C450FifthRadialC10.bound
  · exact C450FifthRadialC11.bound
  · exact C450FifthRadialC12.bound
  · exact C450FifthRadialC13.bound
  · exact C450FifthRadialC14.bound
  · exact C450FifthRadialC15.bound
  · exact C450FifthRadialC16.bound
theorem model_eq0 (r : ℝ) : model (params 0) r =
    angularModel W0.a0 (coefficient W1 (cells 0)) (offset (3/250) (2/125) (cells 0)) r := by
  change model C450FifthRadialC01.params r =
    angularModel W0.a0 (coefficient W1 ⟨-1,(-7/8)⟩) (offset (3/250) (2/125) ⟨-1,(-7/8)⟩) r
  norm_num [model,C450FifthRadialC01.params,coefficient,offset,tailSup,
    W0,W1,fifth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq1 (r : ℝ) : model (params 1) r =
    angularModel W0.a0 (coefficient W1 (cells 1)) (offset (3/250) (2/125) (cells 1)) r := by
  change model C450FifthRadialC02.params r =
    angularModel W0.a0 (coefficient W1 ⟨(-7/8),(-3/4)⟩) (offset (3/250) (2/125) ⟨(-7/8),(-3/4)⟩) r
  norm_num [model,C450FifthRadialC02.params,coefficient,offset,tailSup,
    W0,W1,fifth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq2 (r : ℝ) : model (params 2) r =
    angularModel W0.a0 (coefficient W1 (cells 2)) (offset (3/250) (2/125) (cells 2)) r := by
  change model C450FifthRadialC03.params r =
    angularModel W0.a0 (coefficient W1 ⟨(-3/4),(-5/8)⟩) (offset (3/250) (2/125) ⟨(-3/4),(-5/8)⟩) r
  norm_num [model,C450FifthRadialC03.params,coefficient,offset,tailSup,
    W0,W1,fifth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq3 (r : ℝ) : model (params 3) r =
    angularModel W0.a0 (coefficient W1 (cells 3)) (offset (3/250) (2/125) (cells 3)) r := by
  change model C450FifthRadialC04.params r =
    angularModel W0.a0 (coefficient W1 ⟨(-5/8),(-1/2)⟩) (offset (3/250) (2/125) ⟨(-5/8),(-1/2)⟩) r
  norm_num [model,C450FifthRadialC04.params,coefficient,offset,tailSup,
    W0,W1,fifth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq4 (r : ℝ) : model (params 4) r =
    angularModel W0.a0 (coefficient W1 (cells 4)) (offset (3/250) (2/125) (cells 4)) r := by
  change model C450FifthRadialC05.params r =
    angularModel W0.a0 (coefficient W1 ⟨(-1/2),(-3/8)⟩) (offset (3/250) (2/125) ⟨(-1/2),(-3/8)⟩) r
  norm_num [model,C450FifthRadialC05.params,coefficient,offset,tailSup,
    W0,W1,fifth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq5 (r : ℝ) : model (params 5) r =
    angularModel W0.a0 (coefficient W1 (cells 5)) (offset (3/250) (2/125) (cells 5)) r := by
  change model C450FifthRadialC06.params r =
    angularModel W0.a0 (coefficient W1 ⟨(-3/8),(-1/4)⟩) (offset (3/250) (2/125) ⟨(-3/8),(-1/4)⟩) r
  norm_num [model,C450FifthRadialC06.params,coefficient,offset,tailSup,
    W0,W1,fifth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq6 (r : ℝ) : model (params 6) r =
    angularModel W0.a0 (coefficient W1 (cells 6)) (offset (3/250) (2/125) (cells 6)) r := by
  change model C450FifthRadialC07.params r =
    angularModel W0.a0 (coefficient W1 ⟨(-1/4),(-1/8)⟩) (offset (3/250) (2/125) ⟨(-1/4),(-1/8)⟩) r
  norm_num [model,C450FifthRadialC07.params,coefficient,offset,tailSup,
    W0,W1,fifth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq7 (r : ℝ) : model (params 7) r =
    angularModel W0.a0 (coefficient W1 (cells 7)) (offset (3/250) (2/125) (cells 7)) r := by
  change model C450FifthRadialC08.params r =
    angularModel W0.a0 (coefficient W1 ⟨(-1/8),0⟩) (offset (3/250) (2/125) ⟨(-1/8),0⟩) r
  norm_num [model,C450FifthRadialC08.params,coefficient,offset,tailSup,
    W0,W1,fifth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq8 (r : ℝ) : model (params 8) r =
    angularModel W0.a0 (coefficient W1 (cells 8)) (offset (3/250) (2/125) (cells 8)) r := by
  change model C450FifthRadialC09.params r =
    angularModel W0.a0 (coefficient W1 ⟨0,(1/8)⟩) (offset (3/250) (2/125) ⟨0,(1/8)⟩) r
  norm_num [model,C450FifthRadialC09.params,coefficient,offset,tailSup,
    W0,W1,fifth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq9 (r : ℝ) : model (params 9) r =
    angularModel W0.a0 (coefficient W1 (cells 9)) (offset (3/250) (2/125) (cells 9)) r := by
  change model C450FifthRadialC10.params r =
    angularModel W0.a0 (coefficient W1 ⟨(1/8),(1/4)⟩) (offset (3/250) (2/125) ⟨(1/8),(1/4)⟩) r
  norm_num [model,C450FifthRadialC10.params,coefficient,offset,tailSup,
    W0,W1,fifth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq10 (r : ℝ) : model (params 10) r =
    angularModel W0.a0 (coefficient W1 (cells 10)) (offset (3/250) (2/125) (cells 10)) r := by
  change model C450FifthRadialC11.params r =
    angularModel W0.a0 (coefficient W1 ⟨(1/4),(3/8)⟩) (offset (3/250) (2/125) ⟨(1/4),(3/8)⟩) r
  norm_num [model,C450FifthRadialC11.params,coefficient,offset,tailSup,
    W0,W1,fifth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq11 (r : ℝ) : model (params 11) r =
    angularModel W0.a0 (coefficient W1 (cells 11)) (offset (3/250) (2/125) (cells 11)) r := by
  change model C450FifthRadialC12.params r =
    angularModel W0.a0 (coefficient W1 ⟨(3/8),(1/2)⟩) (offset (3/250) (2/125) ⟨(3/8),(1/2)⟩) r
  norm_num [model,C450FifthRadialC12.params,coefficient,offset,tailSup,
    W0,W1,fifth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq12 (r : ℝ) : model (params 12) r =
    angularModel W0.a0 (coefficient W1 (cells 12)) (offset (3/250) (2/125) (cells 12)) r := by
  change model C450FifthRadialC13.params r =
    angularModel W0.a0 (coefficient W1 ⟨(1/2),(5/8)⟩) (offset (3/250) (2/125) ⟨(1/2),(5/8)⟩) r
  norm_num [model,C450FifthRadialC13.params,coefficient,offset,tailSup,
    W0,W1,fifth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq13 (r : ℝ) : model (params 13) r =
    angularModel W0.a0 (coefficient W1 (cells 13)) (offset (3/250) (2/125) (cells 13)) r := by
  change model C450FifthRadialC14.params r =
    angularModel W0.a0 (coefficient W1 ⟨(5/8),(3/4)⟩) (offset (3/250) (2/125) ⟨(5/8),(3/4)⟩) r
  norm_num [model,C450FifthRadialC14.params,coefficient,offset,tailSup,
    W0,W1,fifth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq14 (r : ℝ) : model (params 14) r =
    angularModel W0.a0 (coefficient W1 (cells 14)) (offset (3/250) (2/125) (cells 14)) r := by
  change model C450FifthRadialC15.params r =
    angularModel W0.a0 (coefficient W1 ⟨(3/4),(7/8)⟩) (offset (3/250) (2/125) ⟨(3/4),(7/8)⟩) r
  norm_num [model,C450FifthRadialC15.params,coefficient,offset,tailSup,
    W0,W1,fifth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq15 (r : ℝ) : model (params 15) r =
    angularModel W0.a0 (coefficient W1 (cells 15)) (offset (3/250) (2/125) (cells 15)) r := by
  change model C450FifthRadialC16.params r =
    angularModel W0.a0 (coefficient W1 ⟨(7/8),1⟩) (offset (3/250) (2/125) ⟨(7/8),1⟩) r
  norm_num [model,C450FifthRadialC16.params,coefficient,offset,tailSup,
    W0,W1,fifth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq (i : Case) (r : ℝ) : model (params i) r =
    angularModel W0.a0 (coefficient W1 (cells i)) (offset (3/250) (2/125) (cells i)) r := by
  fin_cases i
  · exact model_eq0 r
  · exact model_eq1 r
  · exact model_eq2 r
  · exact model_eq3 r
  · exact model_eq4 r
  · exact model_eq5 r
  · exact model_eq6 r
  · exact model_eq7 r
  · exact model_eq8 r
  · exact model_eq9 r
  · exact model_eq10 r
  · exact model_eq11 r
  · exact model_eq12 r
  · exact model_eq13 r
  · exact model_eq14 r
  · exact model_eq15 r
theorem radial_paid (i : Case) : CellRadialBound W0 W1 (3/250) (2/125) (cells i) := by
  intro r hr0 hr1
  have hb := model_bound i r ⟨hr0,hr1⟩
  rw [model_eq] at hb
  have hc := cap_lt_actual (params i) (params_valid i)
  have ha : ((params i).A:ℝ) = W0.a0 := by
    change ((params i).A:ℝ) = (fifth.a0:ℝ)
    exact congrArg (fun x : ℚ => (x:ℝ)) (params_A i)
  have hbb : ((params i).B:ℝ) = W1.a0 := by
    change ((params i).B:ℝ) = (fifth.b0:ℝ)
    exact congrArg (fun x : ℚ => (x:ℝ)) (params_B i)
  rw [ha,hbb] at hc
  exact hb.trans hc
theorem fifth_paid : SegmentNormalized fifth := by
  intro h0 h1
  have hp := normalized_of_cells cells cells_valid cells_cover W0 W1
    (by norm_num [W0,fifth,c450Segs,TenSeg.W0])
    (by norm_num [W0,fifth,c450Segs,TenSeg.W0])
    (by norm_num [W0,fifth,c450Segs,TenSeg.W0])
    (by norm_num [W1,fifth,c450Segs,TenSeg.W1])
    (3/250) (2/125) (by norm_num) (by norm_num) radial_paid
  have he0 : (fifth.eLo:ℝ) = (3/250:ℝ) := by norm_num [fifth,c450Segs]
  have he1 : (fifth.eHi:ℝ) = (2/125:ℝ) := by norm_num [fifth,c450Segs]
  rw [he0,he1]
  exact hp
def remainingSegs : List TenSeg := c450Segs.drop 5
theorem remaining_count : remainingSegs.length = 31 := by decide +kernel
theorem fourth_remaining_split : C450FourthSegment.remainingSegs = fifth :: remainingSegs := rfl
def RemainingSourceObligation : Prop := ∀ s ∈ remainingSegs, SegmentNormalized s
theorem fourth_remaining_of_remaining (hr : RemainingSourceObligation) :
    C450FourthSegment.RemainingSourceObligation := by
  intro s hs
  rw [fourth_remaining_split] at hs
  simp only [List.mem_cons] at hs
  rcases hs with hfifth | hrest
  · rw [hfifth]
    exact fifth_paid
  · exact hr s hrest
theorem source_of_remaining (hr : RemainingSourceObligation) : SourceObligation :=
  C450FourthSegment.source_of_remaining (fourth_remaining_of_remaining hr)
theorem atom_of_remaining (hr : RemainingSourceObligation) : C450Atom :=
  atom_of_source (source_of_remaining hr)
end N11Formalization.C450FifthSegment
#check @N11Formalization.C450FifthSegment.fifth_paid
#check @N11Formalization.C450FifthSegment.atom_of_remaining
#print axioms N11Formalization.C450FifthSegment.cells_cover
#print axioms N11Formalization.C450FifthSegment.radial_paid
#print axioms N11Formalization.C450FifthSegment.fifth_paid
#print axioms N11Formalization.C450FifthSegment.atom_of_remaining
