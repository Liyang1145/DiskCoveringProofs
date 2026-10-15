import Mathlib
import N11Formalization.FlashLeafRootNetwork
import N11Formalization.Conditional.RootSpec
import N11Formalization.RootRangeBoxFull

/-!
# FlashLeafRootSpec -- the S-level oracle consumer on the ACTUAL C891 root

This is the S-level instantiation of the frozen target
`N11Formalization.FlashLeafRootNetwork.oracle_le_sq`, which states

    V2 (canonAnchors u) <= (u 6)^2

for `u` in the certificate box with `residual u = 0` (the boundary/face feasibility of the
canonical 51-edge network, `hF0` supplied by the proved fixed rational point `O0`).

Here we remove the four explicit hypotheses by deriving them from the actual root `S.root` of
`C891RootSpec`, and rewrite the radius to `Rstar S`.  `canonAnchors` is the exact chart object
built from `TCSystem.thetaOf`/`arcEnd` (not a numeric leaf): canonical anchor `j` is
`arcEnd u (j + 2)`.

Nothing about an arbitrary cover is assumed or concluded.
-/

namespace N11Formalization.FlashLeafRootSpec

open N11Formalization

/-- `InCertBox S.root` from the spec's box membership and the two box identifications. -/
theorem inCertBox_root (S : C891RootSpec) (hlo : S.boxLo = boxLoCert) (hhi : S.boxHi = boxHiCert) :
    RootRangeBoxFull.InCertBox S.root := by
  intro i
  have h := S.root_mem.1 i
  rw [hlo, hhi] at h
  exact h

/-- `residual S.root = 0` from `sys = TCSystem` and the root equation (first 5 components). -/
theorem residual_root (S : C891RootSpec) (hsys : S.sys = TCSystem) : residual S.root = 0 := by
  have hz : TCSystem S.root = 0 := by
    rw [← hsys]
    exact S.root_mem.2
  funext i
  have h1 := TCSystem_first S.root i
  have h2 : TCSystem S.root ⟨(i : ℕ), by omega⟩ = 0 := by rw [hz]; rfl
  rw [h1] at h2
  exact h2

/-- **The S-level oracle consumer on the actual root**: the canonical candidate configuration at
`S.root` obeys `V2 <= (Rstar S)^2`.  All four hypotheses of the frozen target are discharged here
(`InCertBox` and `residual = 0` from the spec; `hsin`/`hR` from `rootRange_of_box`). -/
theorem oracle_le_sq_root (S : C891RootSpec) (hsys : S.sys = TCSystem)
    (hlo : S.boxLo = boxLoCert) (hhi : S.boxHi = boxHiCert) (hidx : S.radiusIndex = 6) :
    ResumeNetwork.V2 (FlashRootNetwork.canonAnchors S.root) ≤ (Rstar S) ^ 2 := by
  have hu : RootRangeBoxFull.InCertBox S.root := inCertBox_root S hlo hhi
  have hres : residual S.root = 0 := residual_root S hsys
  have HR : RootRange S.root := RootRangeBoxFull.rootRange_of_box S.root hu
  have hmain : ResumeNetwork.V2 (FlashRootNetwork.canonAnchors S.root) ≤ (S.root 6) ^ 2 :=
    FlashRootNetwork.oracle_le_sq S.root hu hres HR.hsin HR.hR
  rwa [show Rstar S = S.root 6 from by rw [Rstar, hidx]] at hmain

end N11Formalization.FlashLeafRootSpec

#print axioms N11Formalization.FlashLeafRootSpec.oracle_le_sq_root
#print axioms N11Formalization.FlashLeafRootSpec.residual_root
#print axioms N11Formalization.FlashLeafRootSpec.inCertBox_root
