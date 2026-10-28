import N11Formalization.ActualIncidentFacetGerms

/-! Same-primal-witness chord geometry. A circle meets a line through two
distinct sites in those two sites only. Strict supporting sides cannot cross
any other incident chord internally, and two distinct fan spokes sharing an
apex cannot cross internally. Complements the distinct-witness crossing lemma. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualIncidentChordGeometry
open ActualVoronoiCells ActualVoronoiIncidence ActualHubEdgeGeometry
open ActualHubEdgeEndpointGeometry ActualIncidentFacetGerms

theorem circle_line_two {v a b k : Point} (hab : a ≠ b)
    (hb : dist v a = dist v b) (hk : dist v k = dist v a)
    {t : ℝ} (ht : k-a = t • (b-a)) : k = a ∨ k = b := by
  have hdn : 0 < ‖b-a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)
  have hB := translated_bisector hb
  have hK := translated_bisector hk.symm
  rw [ht,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,real_inner_smul_right] at hK
  have hscaled : t*‖b-a‖^2 = 2*t*inner ℝ (v-a) (b-a) := by rw [hB]; ring
  have hf : t*(t-1)*‖b-a‖^2 = 0 := by nlinarith
  have hn : ‖b-a‖^2 ≠ 0 := (sq_pos_of_pos hdn).ne'
  have hp : t*(t-1) = 0 := (mul_eq_zero.mp hf).resolve_right hn
  rcases mul_eq_zero.mp hp with ht0 | ht1
  · left
    rw [ht0,zero_smul] at ht
    exact sub_eq_zero.mp ht
  · right
    have htone : t = 1 := by linarith
    rw [htone,one_smul] at ht
    exact sub_left_inj.mp ht

theorem incident_chord_noncollinear {c : Fin 11 → Point} (hc : Function.Injective c)
    {v : Point} {i j k : Fin 11} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hi : i ∈ incident c v) (hj : j ∈ incident c v) (hk : k ∈ incident c v) :
    inner ℝ (c k-c i) (perp (c j-c i)) ≠ 0 := by
  intro he
  have hd : c j-c i ≠ 0 := sub_ne_zero.mpr (fun h => hij (hc h).symm)
  have hp := perp_ne hd
  have hdorth : inner ℝ (c j-c i) (perp (c j-c i)) = 0 := by
    rw [real_inner_comm,perp_inner]
  obtain ⟨t,ht⟩ := parallel_of_orthogonal hd hp hdorth he
  rcases circle_line_two (fun h => hij (hc h))
    (le_antisymm ((mem_incident.mp hi) j) ((mem_incident.mp hj) i))
    (le_antisymm ((mem_incident.mp hk) i) ((mem_incident.mp hi) k)) ht with h | h
  · exact hki (hc h)
  · exact hkj (hc h)

theorem supporting_chord_no_internal_crossing {c : Fin 11 → Point} {v d : Point}
    {i j k l : Fin 11} (hd : d ∈ PairCone c v i j)
    (hk : k ∈ incident c v) (hl : l ∈ incident c v)
    {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (hpoint : s • c i+(1-s) • c j = t • c k+(1-t) • c l) :
    (k = i ∨ k = j) ∧ (l = i ∨ l = j) := by
  have hij : inner ℝ d (c j) = inner ℝ d (c i) := by
    have h := hd.1
    rw [inner_sub_right] at h
    linarith
  have hle (a : Fin 11) (ha : a ∈ incident c v) :
      inner ℝ d (c a) ≤ inner ℝ d (c i) := by
    by_cases hai : a = i
    · rw [hai]
    by_cases haj : a = j
    · rw [haj,hij]
    have hh := hd.2 a ha hai haj
    rw [inner_sub_right] at hh
    linarith
  have hK := hle k hk
  have hL := hle l hl
  have he := congrArg (fun x : Point => inner ℝ d x) hpoint
  simp only [inner_add_right,real_inner_smul_right] at he
  rw [hij] at he
  have hKeq : inner ℝ d (c k) = inner ℝ d (c i) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1-t) (sub_nonneg.mpr hL)]
  have hLeq : inner ℝ d (c l) = inner ℝ d (c i) := by
    nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr hK)]
  have hpair (a : Fin 11) (ha : a ∈ incident c v)
      (haeq : inner ℝ d (c a) = inner ℝ d (c i)) : a = i ∨ a = j := by
    by_contra hnot
    push_neg at hnot
    have hh := hd.2 a ha hnot.1 hnot.2
    rw [inner_sub_right,haeq,sub_self] at hh
    exact (lt_irrefl 0) hh
  exact ⟨hpair k hk hKeq,hpair l hl hLeq⟩

theorem fan_spokes_no_internal_crossing {c : Fin 11 → Point} (hc : Function.Injective c)
    {v : Point} {i j k : Fin 11} (hij : i ≠ j) (hki : k ≠ i)
    (hi : i ∈ incident c v) (hj : j ∈ incident c v) (hk : k ∈ incident c v)
    {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (hpoint : s • c i+(1-s) • c j = t • c i+(1-t) • c k) : k = j := by
  have htne : 1-t ≠ 0 := by linarith
  have hraw : (1-t) • (c k-c i) = (1-s) • (c j-c i) := by
    have h1 : (1-t) • (c k-c i) = (t • c i+(1-t) • c k)-c i := by module
    have h2 : (1-s) • (c j-c i) = (s • c i+(1-s) • c j)-c i := by module
    rw [h1,h2,hpoint]
  have hscaled := congrArg (fun x : Point => (1-t)⁻¹ • x) hraw
  simp only [smul_smul,inv_mul_cancel₀ htne,one_smul] at hscaled
  rcases circle_line_two (fun h => hij (hc h))
    (le_antisymm ((mem_incident.mp hi) j) ((mem_incident.mp hj) i))
    (le_antisymm ((mem_incident.mp hk) i) ((mem_incident.mp hi) k)) hscaled with he | he
  · exact (hki (hc he)).elim
  · exact hc he

end N11Formalization.ActualIncidentChordGeometry
#check @N11Formalization.ActualIncidentChordGeometry.incident_chord_noncollinear
#check @N11Formalization.ActualIncidentChordGeometry.supporting_chord_no_internal_crossing
#check @N11Formalization.ActualIncidentChordGeometry.fan_spokes_no_internal_crossing
#print axioms N11Formalization.ActualIncidentChordGeometry.incident_chord_noncollinear
#print axioms N11Formalization.ActualIncidentChordGeometry.supporting_chord_no_internal_crossing
#print axioms N11Formalization.ActualIncidentChordGeometry.fan_spokes_no_internal_crossing
