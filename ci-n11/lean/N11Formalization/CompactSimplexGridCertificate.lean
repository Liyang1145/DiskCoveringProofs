import N11Formalization.CompactBoxGridCertificate

/-! Finite grids on the entire closed three-angle simplex. The two floor
coordinates stay below the genuine coordinates, so the residual third
angle stays nonnegative. A rational upper replacement of the angle sum
costs only its explicit one-coordinate Lipschitz margin. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.CompactSimplexGridCertificate
open MetricAreaGridCertificate

def Index (N : ℕ) := {k : Fin (N+1) × Fin (N+1) // k.1.val+k.2.val ≤ N}

def node (U : ℝ) (N : ℕ) (k : Index N) : Fin 3 → ℝ :=
  ![gridPoint U N k.val.1,gridPoint U N k.val.2,
    U-gridPoint U N k.val.1-gridPoint U N k.val.2]

def Simplex (U : ℝ) (a : Fin 3 → ℝ) : Prop :=
  (∀ s, 0 ≤ a s) ∧ (∑ s : Fin 3, a s)=U

theorem floor_grid_cover {U x : ℝ} {N : ℕ}
    (hU : 0 < U) (hN : 0 < N) (hx : x ∈ Set.Icc (0 : ℝ) U) :
    ∃ k : Fin (N+1), 0 ≤ x-gridPoint U N k ∧ x-gridPoint U N k ≤ U/(N : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let q : ℝ := x*(N : ℝ)/U
  have hq0 : 0 ≤ q := div_nonneg (mul_nonneg hx.1 hNr.le) hU.le
  have hqN : q ≤ N := by
    dsimp [q]
    apply (div_le_iff₀ hU).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hx.2 hNr.le]
  let k : Fin (N+1) := ⟨Nat.floor q,by have hh := Nat.floor_le_of_le hqN; omega⟩
  have he : x-gridPoint U N k = U/(N : ℝ)*(q-(Nat.floor q : ℝ)) := by
    change x-U*(Nat.floor q : ℝ)/(N : ℝ)=_
    dsimp [q]
    field_simp [hU.ne',hNr.ne']
  have hb := Nat.abs_sub_floor_le hq0
  have hlo := Nat.floor_le hq0
  have hn : 0 ≤ U/(N : ℝ) := div_nonneg hU.le hNr.le
  refine ⟨k,?_,?_⟩
  · rw [he]
    exact mul_nonneg hn (sub_nonneg.mpr hlo)
  · rw [he]
    have hh := (le_abs_self (q-(Nat.floor q : ℝ))).trans hb
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hn

theorem node_simplex {U : ℝ} {N : ℕ} (hU : 0 ≤ U) (hN : 0 < N) (k : Index N) :
    Simplex U (node U N k) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hk : (k.val.1.val : ℝ)+(k.val.2.val : ℝ) ≤ N := by exact_mod_cast k.property
  have hg : gridPoint U N k.val.1+gridPoint U N k.val.2 ≤ U := by
    unfold gridPoint
    rw [← add_div]
    apply (div_le_iff₀ hNr).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hk hU]
  constructor
  · intro s
    fin_cases s
    · exact (CompactBoxGridCertificate.gridPoint_mem hU hN k.val.1).1
    · exact (CompactBoxGridCertificate.gridPoint_mem hU hN k.val.2).1
    · change 0 ≤ U-gridPoint U N k.val.1-gridPoint U N k.val.2
      linarith only [hg]
  · simp [node,Fin.sum_univ_three]

theorem simplex_grid_cover {U : ℝ} {N : ℕ} {a : Fin 3 → ℝ}
    (hU : 0 < U) (hN : 0 < N) (ha : Simplex U a) :
    ∃ k : Index N, |a 0-node U N k 0| ≤ U/(N : ℝ) ∧
      |a 1-node U N k 1| ≤ U/(N : ℝ) ∧
      |a 2-node U N k 2| ≤ 2*U/(N : ℝ) := by
  have hsum : a 0+a 1+a 2=U := by simpa [Fin.sum_univ_three] using ha.2
  have ha0 : a 0 ∈ Set.Icc (0 : ℝ) U := ⟨ha.1 0,by linarith [ha.1 1,ha.1 2]⟩
  have ha1 : a 1 ∈ Set.Icc (0 : ℝ) U := ⟨ha.1 1,by linarith [ha.1 0,ha.1 2]⟩
  obtain ⟨j,hj0,hj⟩ := floor_grid_cover hU hN ha0
  obtain ⟨l,hl0,hl⟩ := floor_grid_cover hU hN ha1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hg : gridPoint U N j+gridPoint U N l ≤ U := by linarith [ha.1 2]
  have hk : j.val+l.val ≤ N := by
    have hh : U*((j.val : ℝ)+(l.val : ℝ)) ≤ U*(N : ℝ) := by
      have ht := (div_le_iff₀ hNr).mp (show
        (U*(j.val : ℝ)+U*(l.val : ℝ))/(N : ℝ) ≤ U by simpa [gridPoint,add_div] using hg)
      nlinarith only [ht]
    have ht := (mul_le_mul_iff_right₀ hU).mp hh
    exact_mod_cast ht
  let k : Index N := ⟨(j,l),hk⟩
  refine ⟨k,?_,?_,?_⟩
  · simpa [k,node,abs_of_nonneg hj0] using hj
  · simpa [k,node,abs_of_nonneg hl0] using hl
  · have he : a 2-(U-gridPoint U N j-gridPoint U N l)=
        -((a 0-gridPoint U N j)+(a 1-gridPoint U N l)) := by linarith only [hsum]
    change |a 2-(U-gridPoint U N j-gridPoint U N l)| ≤ 2*U/(N : ℝ)
    rw [he,abs_neg,abs_of_nonneg (add_nonneg hj0 hl0)]
    have hh := add_le_add hj hl
    simpa only [← two_mul,← mul_div_assoc] using hh

theorem simplex_upper_of_grid {U M : ℝ} {N : ℕ} (hU : 0 < U) (hN : 0 < N)
    (L : Fin 3 → ℝ) (hL : ∀ s, 0 ≤ L s) (f : (Fin 3 → ℝ) → ℝ)
    (hlip : ∀ a b, |f a-f b| ≤ ∑ s : Fin 3, L s*|a s-b s|)
    (hnodes : ∀ k : Index N, f (node U N k) ≤ M) :
    ∀ a, Simplex U a → f a ≤ M+(L 0+L 1+2*L 2)*U/(N : ℝ) := by
  intro a ha
  obtain ⟨k,h0,h1,h2⟩ := simplex_grid_cover hU hN ha
  have hh := hlip a (node U N k)
  rw [Fin.sum_univ_three] at hh
  have h0' := mul_le_mul_of_nonneg_left h0 (hL 0)
  have h1' := mul_le_mul_of_nonneg_left h1 (hL 1)
  have h2' := mul_le_mul_of_nonneg_left h2 (hL 2)
  have hm := add_le_add (add_le_add h0' h1') h2'
  have he : L 0*(U/(N : ℝ))+L 1*(U/(N : ℝ))+L 2*(2*U/(N : ℝ)) =
      (L 0+L 1+2*L 2)*U/(N : ℝ) := by ring
  rw [he] at hm
  have hd := le_abs_self (f a-f (node U N k))
  linarith only [hh,hm,hd,hnodes k]

theorem pi_simplex_upper_of_grid {U P M : ℝ} {N : ℕ}
    (hU : Real.pi ≤ U) (hP : P ≤ Real.pi) (hN : 0 < N)
    (L : Fin 3 → ℝ) (hL : ∀ s, 0 ≤ L s) (f : (Fin 3 → ℝ) → ℝ)
    (hlip : ∀ a b, |f a-f b| ≤ ∑ s : Fin 3, L s*|a s-b s|)
    (hnodes : ∀ k : Index N, f (node U N k) ≤ M) :
    ∀ a, Simplex Real.pi a → f a ≤
      M+(L 0+L 1+2*L 2)*U/(N : ℝ)+L 2*(U-P) := by
  intro a ha
  let b : Fin 3 → ℝ := ![a 0,a 1,a 2+(U-Real.pi)]
  have hb : Simplex U b := by
    constructor
    · intro s
      fin_cases s
      · exact ha.1 0
      · exact ha.1 1
      · change 0 ≤ a 2+(U-Real.pi)
        linarith [ha.1 2]
    · have hs := ha.2
      simp only [Fin.sum_univ_three] at hs
      simpa [b,Fin.sum_univ_three] using (show a 0+a 1+(a 2+(U-Real.pi))=U by linarith only [hs])
  have hf := simplex_upper_of_grid (Real.pi_pos.trans_le hU) hN L hL f hlip hnodes b hb
  have hh := hlip a b
  have he : |a 2-(a 2+(U-Real.pi))|=U-Real.pi := by
    rw [show a 2-(a 2+(U-Real.pi))=-(U-Real.pi) by ring,abs_neg,
      abs_of_nonneg (sub_nonneg.mpr hU)]
  rw [Fin.sum_univ_three] at hh
  change |f a-f b| ≤ L 0*|a 0-a 0|+L 1*|a 1-a 1|+L 2*|a 2-(a 2+(U-Real.pi))| at hh
  simp only [sub_self,abs_zero,mul_zero,zero_add,he] at hh
  have hd := le_abs_self (f a-f b)
  have hp := mul_le_mul_of_nonneg_left (sub_le_sub_left hP U) (hL 2)
  linarith only [hf,hh,hd,hp]

end N11Formalization.CompactSimplexGridCertificate
#check @N11Formalization.CompactSimplexGridCertificate.pi_simplex_upper_of_grid
#print axioms N11Formalization.CompactSimplexGridCertificate.simplex_grid_cover
#print axioms N11Formalization.CompactSimplexGridCertificate.pi_simplex_upper_of_grid
