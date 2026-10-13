# Radius-deficit audit — corrected in place (v2)
# Scope: members/topology-audit-cc2/radius-deficit-audit/. Lead proofs unchanged.
# Inputs (read-only): lead/{RADIUS-DEFICIT-LEMMA, RADIUS-DEFICIT-INTERFACE,
# FACE-ANGLE-INTERFACE-DRAFT, AREA-SAFE-RELAXATION}.md. No claims registered.

## 0. Legal domain
Unit disk D, covering radius r ≤ U; every interior Voronoi vertex O_f is a point of D covered at
radius U, so |O_f − s| ≤ U for each site s incident to it; hence R_f ≤ U for every interior dual
face. All statements below are in this domain.

## 1. Corrections of my v1 (all accepted)

C1. **I introduced the sign slip; the lead's formula is correct.** From h(λ) = R_f cos(β/2+λ) −
    R_g cos(β/2−λ) = 0 at λ = ±Δ:
      (R_f − R_g)cos(β/2)cosΔ + (R_f + R_g)sin(β/2)sinΔ = 0
      ⇒ tanΔ = −[(R_f−R_g)/(R_f+R_g)]cot(β/2) = [(R_g−R_f)/(R_f+R_g)]cot(β/2),
    which is exactly the relation displayed in RADIUS-DEFICIT-INTERFACE.md. My v1 dropped the
    minus of −(R_f−R_g) and then reported a "sign slip" in the lead; that report is withdrawn.
C2. **Paired facet area = R_f R_g sinβ, NOT 2R_f R_g sinβ.** Verified directly: P = (0,0),
    Q = (l,0), O_f = (l/2, h_f), O_g = (l/2, −h_g); the angle at P between PO_f and PO_g equals
    π − γ_f − γ_g = β, and |PO_f × PO_g|/2 = (1/2)R_f R_g sinβ for each of the two triangles, so
    the pair (the kite O_f P O_g Q) has R_f R_g sinβ. The AREA-SAFE per-pair budget ρ² sinβ_e is
    the right comparison, and the deficit is D_e := U²(1−xy)sinβ with x = R_f/U, y = R_g/U.
C3. **The needed elementary inequality is |tanΔ| ≥ |Δ|**, not tan(β/2) ≥ |Δ| (false for small β),
    and my v1 identity dropped sin(β/2). Correct chain:
      τ = |tanΔ|·tan(β/2),  tan(β/2) = (1−cosβ)/sinβ  ⇒  τ·sinβ = |tanΔ|(1−cosβ) ≥ |Δ|(1−cosβ).
    With 1−xy ≥ 2τ/(1+τ) ≥ τ (from max(x,y) ≤ 1):  **D_e ≥ U²τ sinβ ≥ U²(1−cosβ)|Δ|**.
C4. **β → π is not a violation.** γ_f,γ_g > 0 force |Δ| < (π−β)/2 → 0, so (1−cosβ)|Δ| → 0 too and
    the bound is continuous. The v1 sentence claiming a violation at β = π is deleted.
C5. **Boundary edges: no automatic transfer.** The second member of a boundary facet pair is the
    anchor (a switch point on S¹) with cell radius ρ, not a triangle with circumcentre O_g and
    opposite angle γ_g; there is no companion relation R_g sinγ_g = l/2. The v1 extension of the
    formula to boundary edges is withdrawn.
C6. **The fan triangulation does not universally add 2m−2 diagonals** (in a generic triangulated
    dual it adds none; 2m−2 is the k10-catalogue convention). Withdrawn as a general statement.
    The usable content stays: inserted diagonals have β = 0 and contribute D_e = 0.
C7. **D_e = 0 also at β = 0 and β = π, and at R_f R_g = U²**, which (with R_f,R_g ≤ U) forces
    R_f = R_g = U. So the statement is: for 0 < β < π, D_e = 0 iff R_f = R_g = U.
C8. **Bindingness is already demonstrated** by C1222's 18 global class exclusions with the full
    Fraction and box-partition replay; my v1 line calling this open predates that result and is
    deleted. (C1222 itself is not re-audited here.)

## 2. Corrected analytic content

**2.1 Delaunay/Voronoi identity.** β_uv = π − γ_1 − γ_2 with bearing arguments π/2 − γ_1 and
γ_2 − π/2 ∈ (−π/2,π/2); valid including obtuse triangles; β ∈ [0,π] from γ_1+γ_2 ≤ π. The lead's
proof needs no acuteness premise.
**2.2 R_f ≤ U is automatic** from coverage of the Voronoi vertex.
**2.3 τ identity.** τ = |x−y|/(x+y) = |tanΔ|tan(β/2); equivalently
tanΔ = [(R_g−R_f)/(R_f+R_g)]cot(β/2).
**2.4 Deficit.** actual pair area R_fR_g sinβ = xy U² sinβ; budget U² sinβ; gap
D_e = U²(1−xy)sinβ. Chain (C3): D_e ≥ U²(1−cosβ)|Δ|, equality in the limit R_f = U; at
R_f = U the sharper form D_e ≥ U²(2τ/(1+τ))sinβ holds.
**2.5 Face imbalance.** Σ_{e⊂f}Δ_fe = (Σ_{e⊂f}β_e − π)/2; Σ_e D_e ≥ (U²/2)m_f|Σβ_e − π|,
m_f = min_e(1−cosβ_e), using |Σy| ≤ Σ|y|; the factor 1/2 is the two-faces-per-interior-edge count,
absent for an edge-disjoint collection.

## 3. Scope
Deficit instrument bites only on genuine interior facets (zero-β inserted diagonals contribute 0);
boundary pairs are outside the proved formula (C5) and need a separate anchor-radius argument.

## 4. Status
Lead lemma and interface correct as written; my v1 had six errors, all listed in §1 and removed.
Corrected chain: D_e = U²(1−xy)sinβ ≥ U²(1−cosβ)|Δ|. No new claims; no grid evidence used.
