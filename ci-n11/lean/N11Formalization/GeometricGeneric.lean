import N11Formalization.PolynomialGeneric

set_option autoImplicit false
noncomputable section
namespace N11Formalization.GeometricGeneric
open N11Formalization PolynomialGeneric MvPolynomial

abbrev Poly := MvPolynomial Coord ℝ
abbrev Test := (Fin 2 ↪ Fin 11) ⊕ ((Fin 3 ↪ Fin 11) ⊕ (Fin 4 ↪ Fin 11))

def Xc (i : Fin 11) (j : Fin 2) : Poly := X (i,j)

def separated (t : Fin 2 ↪ Fin 11) : Poly :=
  (Xc (t 0) 0 - Xc (t 1) 0)^2 + (Xc (t 0) 1 - Xc (t 1) 1)^2

def oriented (t : Fin 3 ↪ Fin 11) : Poly :=
  (Xc (t 1) 0 - Xc (t 0) 0) * (Xc (t 2) 1 - Xc (t 0) 1) -
  (Xc (t 1) 1 - Xc (t 0) 1) * (Xc (t 2) 0 - Xc (t 0) 0)

def incircle (t : Fin 4 ↪ Fin 11) : Poly :=
  let ax := Xc (t 0) 0 - Xc (t 3) 0
  let ay := Xc (t 0) 1 - Xc (t 3) 1
  let bx := Xc (t 1) 0 - Xc (t 3) 0
  let byy := Xc (t 1) 1 - Xc (t 3) 1
  let cx := Xc (t 2) 0 - Xc (t 3) 0
  let cy := Xc (t 2) 1 - Xc (t 3) 1
  ax * (byy * (cx^2+cy^2) - (bx^2+byy^2)*cy) -
    ay * (bx * (cx^2+cy^2) - (bx^2+byy^2)*cx) +
    (ax^2+ay^2)*(bx*cy-byy*cx)

def testPolynomial : Test → Poly
  | .inl t => separated t
  | .inr (.inl t) => oriented t
  | .inr (.inr t) => incircle t

/-- The assignments used to show the source polynomials are genuinely nonzero. -/
def sample2 : Fin 2 → Fin 2 → ℝ := ![![0,0], ![1,0]]
def sample3 : Fin 3 → Fin 2 → ℝ := ![![0,0], ![1,0], ![0,1]]
def sample4 : Fin 4 → Fin 2 → ℝ := fun i j =>
  if i = 0 then 0 else if i = 1 then (if j = 0 then 1 else 0)
  else if i = 2 then (if j = 1 then 1 else 0) else 2

def assign {n : ℕ} (t : Fin n ↪ Fin 11) (Q : Fin n → Fin 2 → ℝ) : Coord → ℝ :=
  fun j => Function.extend t Q (fun _ => 0) j.1 j.2

theorem assign_at {n : ℕ} (t : Fin n ↪ Fin 11) (Q : Fin n → Fin 2 → ℝ)
    (i : Fin n) (j : Fin 2) : assign t Q (t i,j) = Q i j := by
  simp [assign, t.injective.extend_apply]

theorem separated_eval_control (t : Fin 2 ↪ Fin 11) : eval (assign t sample2) (separated t) = 1 := by
  simp [separated, Xc, assign_at, sample2]

theorem oriented_eval_control (t : Fin 3 ↪ Fin 11) : eval (assign t sample3) (oriented t) = 1 := by
  simp [oriented, Xc, assign_at, sample3]

theorem incircle_eval_control (t : Fin 4 ↪ Fin 11) : eval (assign t sample4) (incircle t) = -4 := by
  norm_num [incircle, Xc, assign_at, sample4, Fin.ext_iff]

theorem testPolynomial_nonzero (t : Test) : testPolynomial t ≠ 0 := by
  rcases t with t | t | t
  · intro h
    have hc := separated_eval_control t
    rw [show separated t = 0 from h, map_zero] at hc
    norm_num at hc
  · intro h
    have hc := oriented_eval_control t
    rw [show oriented t = 0 from h, map_zero] at hc
    norm_num at hc
  · intro h
    have hc := incircle_eval_control t
    rw [show incircle t = 0 from h, map_zero] at hc
    norm_num at hc

/-- Generic here is an explicit coordinate polynomial predicate, not a hidden topology axiom. -/
def Generic (c : Fin 11 → Point) : Prop :=
  ∀ t : Test, eval (coordinates c) (testPolynomial t) ≠ 0

theorem generic_dense : Dense {c : Fin 11 → Point | Generic c} :=
  dense_avoiding_polynomials testPolynomial testPolynomial_nonzero

theorem exists_generic_near (c : Fin 11 → Point) (ε : ℝ) (hε : 0 < ε) :
    ∃ d : Fin 11 → Point, dist c d < ε ∧ Generic d :=
  exists_centers_avoiding testPolynomial testPolynomial_nonzero c ε hε

/-- The actual arbitrary-center lower-bound consumer after removing all finite
pair/triple/quadruple polynomial degeneracies at once. -/
theorem lower_bound_of_generic (R r0 : ℝ) (hR0 : R ≤ r0)
    (hgood : ∀ (r : ℝ) (c : Fin 11 → Point), Generic c → 0 ≤ r → r < r0 →
      Covers c r → R ≤ r)
    (r : ℝ) (c : Fin 11 → Point) (hr : 0 ≤ r) (hc : Covers c r) : R ≤ r :=
  CoverDensity.lower_bound_of_dense_class _ generic_dense R r0 hR0 hgood r c hr hc

/-- The 3x3 affine orientation in actual coordinates. -/
def orient (A B C : Point) : ℝ :=
  (B.ofLp 0 - A.ofLp 0)*(C.ofLp 1-A.ofLp 1) -
    (B.ofLp 1-A.ofLp 1)*(C.ofLp 0-A.ofLp 0)

theorem eval_oriented (c : Fin 11 → Point) (t : Fin 3 ↪ Fin 11) :
    eval (coordinates c) (oriented t) = orient (c (t 0)) (c (t 1)) (c (t 2)) := by
  simp [oriented, Xc, coordinates, orient]

theorem generic_orientation_ne (c : Fin 11 → Point) (hc : Generic c) (t : Fin 3 ↪ Fin 11) :
    orient (c (t 0)) (c (t 1)) (c (t 2)) ≠ 0 := by
  rw [← eval_oriented]
  exact hc (.inr (.inl t))

/-- An explicitly embedded pair cannot coincide. -/
theorem generic_pair_ne (c : Fin 11 → Point) (hc : Generic c) (t : Fin 2 ↪ Fin 11) :
    c (t 0) ≠ c (t 1) := by
  intro he
  have hn := hc (.inl t)
  apply hn
  simp only [testPolynomial, separated, Xc, map_add, map_pow, map_sub, eval_X]
  simp [coordinates, he]

/-- The predicate really excludes repeated centers, not just a formal polynomial label. -/
theorem generic_injective (c : Fin 11 → Point) (hc : Generic c) : Function.Injective c := by
  classical
  intro i j he
  by_contra hij
  let t : Fin 2 ↪ Fin 11 := ⟨![i,j], by
    intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exact (hij (by simpa using hab)).elim
    · exact (hij (by simpa using hab.symm)).elim
    · rfl⟩
  exact generic_pair_ne c hc t (by change c i = c j; exact he)

/-- Library collinearity implies the actual coordinate orientation vanishes. -/
theorem orient_eq_zero_of_collinear (A B C : Point)
    (h : Collinear ℝ ({A,B,C} : Set Point)) : orient A B C = 0 := by
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (k := ℝ) (by simp : A ∈ ({A,B,C} : Set Point))).mp h
  obtain ⟨s, hs⟩ := hv B (by simp)
  obtain ⟨t, ht⟩ := hv C (by simp)
  rw [hs, ht]
  simp [orient, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The dense predicate excludes all three-center collinearities in the real affine space. -/
theorem generic_not_collinear (c : Fin 11 → Point) (hc : Generic c) (t : Fin 3 ↪ Fin 11) :
    ¬ Collinear ℝ ({c (t 0), c (t 1), c (t 2)} : Set Point) := by
  intro h
  exact generic_orientation_ne c hc t (orient_eq_zero_of_collinear _ _ _ h)

/-- Four equal distances to one point force the translated incircle polynomial to vanish.
The common distance is arbitrary (including zero); this is not a sampled rank test. -/
theorem eval_incircle_zero_of_equidistant (c : Fin 11 → Point) (t : Fin 4 ↪ Fin 11)
    (Q : Point) (ρ : ℝ) (h : ∀ i : Fin 4, dist (c (t i)) Q = ρ) :
    eval (coordinates c) (incircle t) = 0 := by
  let D := c (t 3)
  let qx := Q.ofLp 0 - D.ofLp 0
  let qy := Q.ofLp 1 - D.ofLp 1
  have he (i : Fin 4) :
      (c (t i)).ofLp 0 ^ 2 - 2 * (c (t i)).ofLp 0 * Q.ofLp 0 + Q.ofLp 0 ^ 2 +
      ((c (t i)).ofLp 1 ^ 2 - 2 * (c (t i)).ofLp 1 * Q.ofLp 1 + Q.ofLp 1 ^ 2) = ρ ^ 2 := by
    have hi := congrArg (fun r : ℝ => r ^ 2) (h i)
    rw [dist_eq_norm, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two] at hi
    simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs] at hi
    nlinarith [hi]
  have hs (i : Fin 4) :
      ((c (t i)).ofLp 0 - D.ofLp 0)^2 + ((c (t i)).ofLp 1 - D.ofLp 1)^2 =
        2 * (((c (t i)).ofLp 0 - D.ofLp 0) * qx +
          ((c (t i)).ofLp 1 - D.ofLp 1) * qy) := by
    dsimp [qx, qy, D]
    nlinarith [he i, he 3]
  simp only [incircle, Xc, map_add, map_sub, map_mul, map_pow, eval_X, coordinates]
  change ((c (t 0)).ofLp 0 - D.ofLp 0) *
      (((c (t 1)).ofLp 1 - D.ofLp 1) *
        (((c (t 2)).ofLp 0 - D.ofLp 0)^2 + ((c (t 2)).ofLp 1 - D.ofLp 1)^2) -
        (((c (t 1)).ofLp 0 - D.ofLp 0)^2 + ((c (t 1)).ofLp 1 - D.ofLp 1)^2) *
          ((c (t 2)).ofLp 1 - D.ofLp 1)) -
    ((c (t 0)).ofLp 1 - D.ofLp 1) *
      (((c (t 1)).ofLp 0 - D.ofLp 0) *
        (((c (t 2)).ofLp 0 - D.ofLp 0)^2 + ((c (t 2)).ofLp 1 - D.ofLp 1)^2) -
        (((c (t 1)).ofLp 0 - D.ofLp 0)^2 + ((c (t 1)).ofLp 1 - D.ofLp 1)^2) *
          ((c (t 2)).ofLp 0 - D.ofLp 0)) +
    (((c (t 0)).ofLp 0 - D.ofLp 0)^2 + ((c (t 0)).ofLp 1 - D.ofLp 1)^2) *
      (((c (t 1)).ofLp 0 - D.ofLp 0) * ((c (t 2)).ofLp 1 - D.ofLp 1) -
        ((c (t 1)).ofLp 1 - D.ofLp 1) * ((c (t 2)).ofLp 0 - D.ofLp 0)) = 0
  rw [hs 0, hs 1, hs 2]
  ring

/-- No four embedded centers lie on any common Euclidean circle. -/
theorem generic_no_four_equidistant (c : Fin 11 → Point) (hc : Generic c)
    (t : Fin 4 ↪ Fin 11) (Q : Point) (ρ : ℝ) :
    ¬ (∀ i : Fin 4, dist (c (t i)) Q = ρ) := by
  intro h
  exact hc (.inr (.inr t)) (eval_incircle_zero_of_equidistant c t Q ρ h)

end N11Formalization.GeometricGeneric
#check @N11Formalization.GeometricGeneric.generic_dense
#check @N11Formalization.GeometricGeneric.exists_generic_near
#check @N11Formalization.GeometricGeneric.lower_bound_of_generic
#check @N11Formalization.GeometricGeneric.generic_orientation_ne
#print axioms N11Formalization.GeometricGeneric.generic_dense
#print axioms N11Formalization.GeometricGeneric.lower_bound_of_generic
#print axioms N11Formalization.GeometricGeneric.generic_orientation_ne
#print axioms N11Formalization.GeometricGeneric.incircle_eval_control
#check @N11Formalization.GeometricGeneric.generic_injective
#check @N11Formalization.GeometricGeneric.generic_not_collinear
#check @N11Formalization.GeometricGeneric.eval_incircle_zero_of_equidistant
#check @N11Formalization.GeometricGeneric.generic_no_four_equidistant
#print axioms N11Formalization.GeometricGeneric.generic_injective
#print axioms N11Formalization.GeometricGeneric.generic_not_collinear
#print axioms N11Formalization.GeometricGeneric.eval_incircle_zero_of_equidistant
#print axioms N11Formalization.GeometricGeneric.generic_no_four_equidistant

