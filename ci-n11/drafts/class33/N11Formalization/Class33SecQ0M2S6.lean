import N11Formalization.Class33SectorReflect
import N11Formalization.Class33SecQ0M2S6Base
import N11Formalization.Class33SecQ0M2S6G0
import N11Formalization.Class33SecQ0M2S6G1
import N11Formalization.Class33SecQ0M2S6G2

/-! Class33 DRAFT (uncompiled): sector tree Class33SecQ0M2S6: skeleton 191 nodes + 96 parts, 1462 leaves. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.Class33SecQ0M2S6
open Class33SectorReflect N11Formalization.Class33SecQ0M2S6Base
def allParts : List (Box × List Tok) := N11Formalization.Class33SecQ0M2S6G0.parts ++ (N11Formalization.Class33SecQ0M2S6G1.parts ++ (N11Formalization.Class33SecQ0M2S6G2.parts))
theorem allOK : partsOK co M allParts = true := by
  simp only [allParts, partsOK_append, N11Formalization.Class33SecQ0M2S6G0.ok,N11Formalization.Class33SecQ0M2S6G1.ok,N11Formalization.Class33SecQ0M2S6G2.ok, Bool.and_self]
def skel : List Tok := [.S 1 (1/2 : ℚ),.S 2 (1/2 : ℚ),.P,.S 1 (1/4 : ℚ),.S 0 (2 : ℚ),.S 0 (1 : ℚ),.S 2 (3/4 : ℚ),.P,.P,.P,.P,.S 0 (2 : ℚ),.S 0 (1 : ℚ),.P,.S 2 (3/4 : ℚ),.P,.P,.P,.S 2 (1/2 : ℚ),.S 2 (1/4 : ℚ),.S 0 (2 : ℚ),.S 0 (1 : ℚ),.S 1 (3/4 : ℚ),.P,.P,.P,.P,.S 0 (2 : ℚ),.S 0 (1 : ℚ),.P,.S 1 (3/4 : ℚ),.P,.P,.P,.S 0 (2 : ℚ),.S 0 (1 : ℚ),.P,.S 0 (3/2 : ℚ),.S 1 (3/4 : ℚ),.P,.S 2 (3/4 : ℚ),.P,.P,.S 1 (3/4 : ℚ),.S 2 (3/4 : ℚ),.P,.S 0 (7/4 : ℚ),.P,.S 1 (5/8 : ℚ),.P,.P,.S 2 (3/4 : ℚ),.S 0 (7/4 : ℚ),.P,.S 2 (5/8 : ℚ),.P,.P,.S 0 (7/4 : ℚ),.S 1 (7/8 : ℚ),.P,.P,.S 1 (7/8 : ℚ),.S 2 (7/8 : ℚ),.P,.S 0 (15/8 : ℚ),.P,.P,.S 2 (7/8 : ℚ),.S 0 (15/8 : ℚ),.P,.P,.S 0 (15/8 : ℚ),.P,.S 1 (15/16 : ℚ),.P,.S 2 (15/16 : ℚ),.P,.P,.S 1 (3/4 : ℚ),.S 2 (3/4 : ℚ),.P,.S 1 (5/8 : ℚ),.P,.S 2 (7/8 : ℚ),.P,.S 0 (5/2 : ℚ),.S 0 (9/4 : ℚ),.P,.P,.P,.S 2 (3/4 : ℚ),.S 2 (5/8 : ℚ),.P,.S 1 (7/8 : ℚ),.P,.S 0 (5/2 : ℚ),.S 0 (9/4 : ℚ),.P,.P,.P,.S 1 (7/8 : ℚ),.S 2 (7/8 : ℚ),.S 0 (5/2 : ℚ),.S 0 (9/4 : ℚ),.P,.P,.P,.S 0 (5/2 : ℚ),.S 0 (9/4 : ℚ),.S 0 (17/8 : ℚ),.P,.S 1 (13/16 : ℚ),.P,.P,.S 0 (19/8 : ℚ),.S 1 (13/16 : ℚ),.P,.P,.P,.P,.S 2 (7/8 : ℚ),.S 0 (5/2 : ℚ),.S 0 (9/4 : ℚ),.S 0 (17/8 : ℚ),.P,.S 2 (13/16 : ℚ),.P,.P,.S 0 (19/8 : ℚ),.S 2 (13/16 : ℚ),.P,.P,.P,.P,.S 0 (5/2 : ℚ),.S 0 (9/4 : ℚ),.S 0 (17/8 : ℚ),.S 1 (15/16 : ℚ),.S 2 (15/16 : ℚ),.P,.P,.S 2 (15/16 : ℚ),.P,.S 0 (33/16 : ℚ),.P,.P,.S 1 (15/16 : ℚ),.S 2 (15/16 : ℚ),.P,.P,.S 2 (15/16 : ℚ),.P,.S 0 (35/16 : ℚ),.S 1 (31/32 : ℚ),.P,.P,.S 1 (31/32 : ℚ),.P,.P,.S 0 (19/8 : ℚ),.S 1 (15/16 : ℚ),.S 2 (15/16 : ℚ),.P,.P,.S 2 (15/16 : ℚ),.P,.S 0 (37/16 : ℚ),.S 1 (31/32 : ℚ),.P,.P,.S 1 (31/32 : ℚ),.P,.P,.S 1 (15/16 : ℚ),.S 2 (15/16 : ℚ),.P,.P,.S 2 (15/16 : ℚ),.P,.S 0 (39/16 : ℚ),.P,.P,.S 0 (11/4 : ℚ),.S 1 (15/16 : ℚ),.P,.S 2 (15/16 : ℚ),.P,.S 0 (21/8 : ℚ),.P,.P,.P]
theorem skel_ok : chkAll co M rootBox skel (allParts.map Prod.fst) = true := by decide +kernel
def certificate : SharedMomentEfficientFactorCertificate.EfficientSectorCertificate co.C co.mu co.dL co.dR co.bL co.bR M :=
  efficient_of_chk co M skel (allParts.map Prod.fst) (partsOK_sound co M allParts allOK) skel_ok
end N11Formalization.Class33SecQ0M2S6
#print axioms N11Formalization.Class33SecQ0M2S6.certificate
