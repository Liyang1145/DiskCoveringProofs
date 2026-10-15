import N11Formalization.RationalBoxSubdivision
import N11Formalization.MetricSectorRationalNodes

/-! A rational midpoint certificate for an arbitrary closed sector cell.
The two normalized radii lie in the full closed unit interval. The angle
may be any real number, and the signed width coefficient is unrestricted.
The midpoint bracket and a proved coordinate Lipschitz margin produce
the continuous cell bound, including coincident endpoints. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.MetricSectorLocalCertificate

open RationalBoxSubdivision MetricSectorRationalNodes MetricSectorBoxCertificate

/-- Finite rational endpoint checks for the two normalized radii. -/
structure RadiusBoxValid (B : Cell (Fin 3)) : Prop where
  left_lo_nonneg : 0 ≤ (B 1).lo
  left_hi_le_one : (B 1).hi ≤ 1
  right_lo_nonneg : 0 ≤ (B 2).lo
  right_hi_le_one : (B 2).hi ≤ 1

/-- No angle restriction is needed for the globally valid regularity bound. -/
structure CellValid (B : Cell (Fin 3)) : Prop where
  intervals : Valid B
  radii : RadiusBoxValid B

def angleLipschitzQ (C mu : ℚ) : ℚ := 1+(19/25)*|C|+|mu|
def radiusLipschitzQ (C d b : ℚ) : ℚ := 1+(19/25)*|C|+2*|d|+|b|

def localErrorQ (C mu dL dR bL bR : ℚ) (B : Cell (Fin 3)) : ℚ :=
  angleLipschitzQ C mu*halfWidth B 0+
    radiusLipschitzQ C dL bL*halfWidth B 1+
      radiusLipschitzQ C dR bR*halfWidth B 2

def localUpperQ (C mu dL dR bL bR : ℚ) (B : Cell (Fin 3))
    (bounds : NodeBounds) : ℚ :=
  sectorUpperQ C mu dL dR bL bR (midpoint B 0) (midpoint B 1)
    (midpoint B 2) bounds+localErrorQ C mu dL dR bL bR B

theorem angleLipschitzQ_cast (C mu : ℚ) :
    (angleLipschitzQ C mu : ℝ) = angleLipschitz C mu := by
  unfold angleLipschitzQ angleLipschitz
  push_cast
  rfl

theorem radiusLipschitzQ_cast (C d b : ℚ) :
    (radiusLipschitzQ C d b : ℝ) = radiusLipschitz C d b := by
  unfold radiusLipschitzQ radiusLipschitz
  push_cast
  rfl

theorem localErrorQ_cast (C mu dL dR bL bR : ℚ) (B : Cell (Fin 3)) :
    (localErrorQ C mu dL dR bL bR B : ℝ) =
      angleLipschitz C mu*(halfWidth B 0 : ℝ)+
        radiusLipschitz C dL bL*(halfWidth B 1 : ℝ)+
          radiusLipschitz C dR bR*(halfWidth B 2 : ℝ) := by
  simp only [localErrorQ,Rat.cast_add,Rat.cast_mul,
    angleLipschitzQ_cast,radiusLipschitzQ_cast]

theorem radii_mem {B : Cell (Fin 3)} {x : Fin 3 → ℝ}
    (hB : RadiusBoxValid B) (hx : Mem B x) :
    x 1 ∈ Set.Icc (0 : ℝ) 1 ∧ x 2 ∈ Set.Icc (0 : ℝ) 1 := by
  have hl0 : (0 : ℝ) ≤ (B 1).lo := by exact_mod_cast hB.left_lo_nonneg
  have hl1 : ((B 1).hi : ℝ) ≤ 1 := by exact_mod_cast hB.left_hi_le_one
  have hr0 : (0 : ℝ) ≤ (B 2).lo := by exact_mod_cast hB.right_lo_nonneg
  have hr1 : ((B 2).hi : ℝ) ≤ 1 := by exact_mod_cast hB.right_hi_le_one
  exact ⟨⟨hl0.trans (hx 1).1,(hx 1).2.trans hl1⟩,
    ⟨hr0.trans (hx 2).1,(hx 2).2.trans hr1⟩⟩

theorem local_change_upper (C mu dL dR bL bR : ℚ)
    {B : Cell (Fin 3)} (hB : CellValid B) {x : Fin 3 → ℝ} (hx : Mem B x) :
    sectorBoxObjective C mu dL dR bL bR x-
      sectorObjective C mu dL dR bL bR (midpoint B 0) (midpoint B 1)
        (midpoint B 2) ≤ (localErrorQ C mu dL dR bL bR B : ℝ) := by
  have hxrad := radii_mem hB.radii hx
  have hmrad := radii_mem hB.radii (midpoint_mem hB.intervals)
  have hdiff := sectorObjective_difference (C : ℝ) mu dL dR bL bR
    (x 0) (midpoint B 0) hxrad.1 hmrad.1 hxrad.2 hmrad.2
  have hLa : (0 : ℝ) ≤ angleLipschitz C mu := by
    unfold angleLipschitz
    positivity
  have hLl : (0 : ℝ) ≤ radiusLipschitz C dL bL := by
    unfold radiusLipschitz
    positivity
  have hLr : (0 : ℝ) ≤ radiusLipschitz C dR bR := by
    unfold radiusLipschitz
    positivity
  have h0 := mul_le_mul_of_nonneg_left (distance_le_halfWidth hx 0) hLa
  have h1 := mul_le_mul_of_nonneg_left (distance_le_halfWidth hx 1) hLl
  have h2 := mul_le_mul_of_nonneg_left (distance_le_halfWidth hx 2) hLr
  rw [localErrorQ_cast]
  exact (le_abs_self _).trans (hdiff.trans (add_le_add (add_le_add h0 h1) h2))

theorem cell_upper_of_node (C mu dL dR bL bR : ℚ)
    {B : Cell (Fin 3)} (hB : CellValid B) (bounds : NodeBounds)
    (hnode : NodeValid (midpoint B 0) (midpoint B 1) (midpoint B 2) bounds) :
    ∀ x, Mem B x → sectorBoxObjective C mu dL dR bL bR x ≤
      (localUpperQ C mu dL dR bL bR B bounds : ℝ) := by
  intro x hx
  have hd := local_change_upper C mu dL dR bL bR hB hx
  have hn := sector_upper_of_node C mu dL dR bL bR hnode
  unfold localUpperQ
  push_cast
  linarith only [hd,hn]

theorem cell_upper_of_rational_certificate (C mu dL dR bL bR M : ℚ)
    {B : Cell (Fin 3)} (hB : CellValid B) (bounds : NodeBounds)
    (hnode : NodeValid (midpoint B 0) (midpoint B 1) (midpoint B 2) bounds)
    (hupper : localUpperQ C mu dL dR bL bR B bounds ≤ M) :
    ∀ x, Mem B x → sectorBoxObjective C mu dL dR bL bR x ≤ (M : ℝ) := by
  intro x hx
  exact (cell_upper_of_node C mu dL dR bL bR hB bounds hnode x hx).trans
    (by exact_mod_cast hupper)

/-- A leaf contains only finite rational comparisons. -/
structure Certificate (C mu dL dR bL bR M : ℚ) (B : Cell (Fin 3)) where
  bounds : NodeBounds
  valid : CellValid B
  midpoint_valid : NodeValid (midpoint B 0) (midpoint B 1) (midpoint B 2) bounds
  upper : localUpperQ C mu dL dR bL bR B bounds ≤ M

theorem Certificate.sound {C mu dL dR bL bR M : ℚ} {B : Cell (Fin 3)}
    (cert : Certificate C mu dL dR bL bR M B) :
    ∀ x, Mem B x → sectorBoxObjective C mu dL dR bL bR x ≤ (M : ℝ) :=
  cell_upper_of_rational_certificate C mu dL dR bL bR M cert.valid cert.bounds
    cert.midpoint_valid cert.upper

theorem subdivision_upper_of_rational_certificate
    {C mu dL dR bL bR M : ℚ} {B : Cell (Fin 3)}
    (tree : RationalBoxSubdivision.Certificate
      (fun D => Nonempty (Certificate C mu dL dR bL bR M D)) B) :
    ∀ x, Mem B x → sectorBoxObjective C mu dL dR bL bR x ≤ (M : ℝ) := by
  apply certificate_sound tree
  intro D hD x hx
  rcases hD with ⟨cert⟩
  exact cert.sound x hx

end N11Formalization.MetricSectorLocalCertificate
#check @N11Formalization.MetricSectorLocalCertificate.cell_upper_of_node
#check @N11Formalization.MetricSectorLocalCertificate.cell_upper_of_rational_certificate
#check @N11Formalization.MetricSectorLocalCertificate.Certificate.sound
#check @N11Formalization.MetricSectorLocalCertificate.subdivision_upper_of_rational_certificate
#print axioms N11Formalization.MetricSectorLocalCertificate.radii_mem
#print axioms N11Formalization.MetricSectorLocalCertificate.local_change_upper
#print axioms N11Formalization.MetricSectorLocalCertificate.cell_upper_of_node
#print axioms N11Formalization.MetricSectorLocalCertificate.cell_upper_of_rational_certificate
#print axioms N11Formalization.MetricSectorLocalCertificate.Certificate.sound
#print axioms N11Formalization.MetricSectorLocalCertificate.subdivision_upper_of_rational_certificate
