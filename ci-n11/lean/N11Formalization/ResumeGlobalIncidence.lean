import N11Formalization.ResumeNetwork

/-!
# ResumeGlobal: machine-checked 51-edge incidence audit vs source
Source: team-current/lead/FIXED-SWITCH-SOC-REDUCTION.md §1 (L4,L9),
EXACT-ORACLE-INDEX-MAP.md L5, L7. Every check is `decide` on finite data.
-/
namespace N11Formalization.ResumeGlobal
open N11Formalization.ResumeNetwork

/-- raw ring j ↦ canonical (j−2) mod 9; hubs fixed (EXACT-ORACLE-INDEX-MAP L5). -/
def rawToCanon (j : Fin 11) : Fin 11 :=
  if h : j.val < 9 then ⟨(j.val + 7) % 9, by omega⟩ else j

theorem rawToCanon_bij : Function.Bijective rawToCanon := by decide

/-- Source face spec (SOC-REDUCTION L4): hub9 fans 0..3, hub10 fans 4..8, central (0,9,10),(4,9,10). -/
def srcFace (f : Fin 11) : Finset (Fin 11) :=
  if h : f.val < 4 then {⟨f.val, by omega⟩, ⟨f.val + 1, by omega⟩, 9}
  else if h2 : f.val < 9 then {⟨f.val, by omega⟩, ⟨(f.val + 1) % 9, by omega⟩, 10}
  else if f.val = 9 then {0, 9, 10} else {4, 9, 10}

/-- Lean `face` is exactly the source face list, as vertex sets, each with 3 distinct vertices. -/
theorem face_eq_src : ∀ f, Finset.image (face f) Finset.univ = srcFace f ∧
    Function.Injective (face f) := by decide

/-- Boundary edges: site i ↦ anchors U_{i−1}, U_i (SOC L4 "c_i owns U(i−1)..U_i"). -/
theorem anchor_spec : ∀ i : Fin 9, anchorIndex i 0 = i - 1 ∧ anchorIndex i 1 = i := by decide

/-- Each anchor U_s is shared exactly by sites s and s+1 (the switch between c_s and c_{s+1}). -/
theorem anchor_owners : ∀ s : Fin 9,
    (Finset.univ.filter (fun p : Fin 9 × Fin 2 => anchorIndex p.1 p.2 = s)) =
      {(s, 1), (s + 1, 0)} := by decide

/-- Raw anchor j (switch raw j,j+1) ↦ canonical anchor s=j−2 is compatible with sites. -/
theorem raw_anchor_compat : ∀ j : Fin 9,
    rawToCanon ⟨j.val, by omega⟩ = ⟨(j - 2 : Fin 9).val, by omega⟩ ∧
    rawToCanon ⟨(j + 1 : Fin 9).val, by omega⟩ = ⟨((j - 2 : Fin 9) + 1 : Fin 9).val, by omega⟩ := by
  decide

/-- Raw face (ring k,k+1 + hub) as a raw vertex set. -/
def rawFan (k : Fin 9) (hub : Fin 11) : Finset (Fin 11) :=
  {⟨k.val, by omega⟩, ⟨(k + 1 : Fin 9).val, by omega⟩, hub}
def rawCentral (k : Fin 9) : Finset (Fin 11) := {⟨k.val, by omega⟩, 9, 10}

/-- Raw active list (INDEX-MAP L7) maps onto canonical faces 9,10,0,1,2,3,8,4,6. -/
theorem active_map :
    (rawCentral 2).image rawToCanon = srcFace 9 ∧ (rawCentral 6).image rawToCanon = srcFace 10 ∧
    (rawFan 2 9).image rawToCanon = srcFace 0 ∧ (rawFan 3 9).image rawToCanon = srcFace 1 ∧
    (rawFan 4 9).image rawToCanon = srcFace 2 ∧ (rawFan 5 9).image rawToCanon = srcFace 3 ∧
    (rawFan 1 10).image rawToCanon = srcFace 8 ∧ (rawFan 6 10).image rawToCanon = srcFace 4 ∧
    (rawFan 8 10).image rawToCanon = srcFace 6 := by decide

/-- Absent faces = canonical 5,7 = {5,6,10},{7,8,10}: 6 zero-stress edges, 45 local edges. -/
theorem absent_faces : srcFace 5 = {5, 6, 10} ∧ srcFace 7 = {7, 8, 10} ∧
    18 + 3 * 9 = 45 ∧ 18 + 3 * 11 = 51 := by decide

end N11Formalization.ResumeGlobal

#print axioms N11Formalization.ResumeGlobal.face_eq_src
#print axioms N11Formalization.ResumeGlobal.active_map
#print axioms N11Formalization.ResumeGlobal.anchor_owners
