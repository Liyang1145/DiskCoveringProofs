import N11Formalization.SourceRawResponsePacket
import N11Formalization.SourceRelativeFluxGeometry

/-! Actual Cmat=Lambda*inner(tangent,circle), without G/H factor2.
Fine source coordinates and actual scalar response provide all64 pinned
entry inputs. Norm/operator readouts are a separate numeric consumer. -/
set_option autoImplicit false
namespace N11Formalization.SourceCrossGeometry
open N11Formalization RatInterval ResumeLocalIncidence SourceResponseFluxIdentity
open SourceRawResponseIntervals SourceRawResponsePacket
noncomputable section

def rawCross (k l : Fin 9) : ℝ :=
  FlashLocal.Cmat sourceResponse sourceAngle (siteMap k) (siteMap l)

theorem circle_source (k : Fin 9) :
    circleMap (sourceAngle (siteMap k))=arcEnd SourceExactRoot.sourceRoot k := by
  have h := sourceAnchors_circle (siteMap k)
  change FlashRootNetwork.canonAnchors SourceExactRoot.sourceRoot (siteMap k)=_ at h
  rw [FlashRootNetwork.hU_siteMap] at h
  exact h.symm

/-- True determinant sign and NO factor2, for every actual raw entry. -/
theorem rawCross_coordinates (k l : Fin 9) :
    rawCross k l=rawResponse k l*
      (-(arcEnd SourceExactRoot.sourceRoot k).ofLp 1*
          (arcEnd SourceExactRoot.sourceRoot l).ofLp 0+
        (arcEnd SourceExactRoot.sourceRoot k).ofLp 0*
          (arcEnd SourceExactRoot.sourceRoot l).ofLp 1) := by
  have ht0 := SourceRelativeFluxGeometry.tangent_source_zero k
  have ht1 := SourceRelativeFluxGeometry.tangent_source_one k
  change (FlashLocal.circleTangent (sourceAngle (siteMap k))).ofLp 0=_ at ht0
  change (FlashLocal.circleTangent (sourceAngle (siteMap k))).ofLp 1=_ at ht1
  unfold rawCross FlashLocal.Cmat
  rw [circle_source,PinTangentGeometry.inner_coords,ht0,ht1]
  rfl

def determinantBox (k l : Fin 9) : RatInterval :=
  add (mul (neg (anchorBox k 1)) (anchorBox l 0))
    (mul (anchorBox k 0) (anchorBox l 1))

theorem determinantBox_mem (k l : Fin 9) :
    (determinantBox k l).Mem
      (-(arcEnd SourceExactRoot.sourceRoot k).ofLp 1*
          (arcEnd SourceExactRoot.sourceRoot l).ofLp 0+
        (arcEnd SourceExactRoot.sourceRoot k).ofLp 0*
          (arcEnd SourceExactRoot.sourceRoot l).ofLp 1) :=
  add_mem (mul_mem (neg_mem (anchorBox_mem k 1)) (anchorBox_mem l 0))
    (mul_mem (anchorBox_mem k 0) (anchorBox_mem l 1))

def crossInput (k l : Fin 8) : RatInterval :=
  mul (RB k.castSucc l.castSucc) (determinantBox k.castSucc l.castSucc)

theorem crossInput_mem (k l : Fin 8) :
    (crossInput k l).Mem (rawCross k.castSucc l.castSucc) := by
  rw [rawCross_coordinates]
  exact mul_mem (RB_mem _ _) (determinantBox_mem _ _)

end
end N11Formalization.SourceCrossGeometry
#check @N11Formalization.SourceCrossGeometry.rawCross_coordinates
#check @N11Formalization.SourceCrossGeometry.crossInput_mem
#print axioms N11Formalization.SourceCrossGeometry.crossInput_mem
