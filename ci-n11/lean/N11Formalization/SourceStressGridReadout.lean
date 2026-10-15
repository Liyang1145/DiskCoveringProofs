import N11Formalization.SourceStressIntervals
import N11Formalization.SourceBoundaryIntervalReadout

/-! Exact staged readouts for the already sound actual stress intervals.
Every proposed literal is compared with the actual expression-tree interval
by kernel arithmetic. Diagnostic numerical outputs do not supply premises. -/
set_option autoImplicit false
namespace N11Formalization.SourceStressGridReadout
open N11Formalization RatInterval SourceStressIntervals
open SourceBoundaryMultiplierIntervals SourceBoundaryIntervalReadout

theorem slope0_eq : slopeI 0=intv (29836/100000) (29837/100000) := by
  unfold slopeI rounded
  nd_eval
theorem slope1_eq : slopeI 1=intv (25465/100000) (25466/100000) := by
  unfold slopeI rounded
  nd_eval
theorem slope2_eq : slopeI 2=intv (19424/100000) (19425/100000) := by
  unfold slopeI rounded
  nd_eval
theorem slope3_eq : slopeI 3=intv (32095/100000) (32096/100000) := by
  unfold slopeI rounded
  nd_eval
theorem slope4_eq : slopeI 4=intv (33785/100000) (33786/100000) := by
  unfold slopeI rounded
  nd_eval

theorem centralA_eq : centralAI=intv (-52092/100000) (-52091/100000) := by
  simp only [centralAI,SourceStressIntervals.centralDen,rounded,div,inv,
    N11Formalization.SourceFanBarycentricSigns.determinantBox,
    N11Formalization.SourceFanBarycentricSigns.centralHBox,
    N11Formalization.SourceFanBarycentricSigns.centralPBox,
    N11Formalization.SourceFanBarycentricSigns.centralQBox]
  nd_eval
theorem centralB_eq : centralBI=intv (-67746/100000) (-67745/100000) := by
  simp only [centralBI,SourceStressIntervals.centralDen,rounded,div,inv,
    N11Formalization.SourceFanBarycentricSigns.determinantBox,
    N11Formalization.SourceFanBarycentricSigns.centralHBox,
    N11Formalization.SourceFanBarycentricSigns.centralPBox,
    N11Formalization.SourceFanBarycentricSigns.centralQBox]
  nd_eval

macro "numerator_endpoint_eval" : tactic =>
  `(tactic|
    (simp only [numeratorBox,fanBox,centralBox,innerBox,
      SourceBoundaryMultiplierIntervals.normalPBox,
      SourceBoundaryMultiplierIntervals.normalQBox,normalCBox,
      SourceBoundarySignBounds.contact,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk]
     simp only [nd_fin_succ_1,nd_fin_succ_2,nd_fin_succ_3,nd_fin_succ_8]
     simp [velocityBox,widthQ,directionQ,Fin.ext_iff,
      ring00,ring01,ring10,ring11,ring20,ring21,ring30,ring31,ring40,ring41,
      ring50,ring51,ring60,ring61,ring70,ring71,ring80,ring81,
      pin10,pin11,pin20,pin21,pin30,pin31,pin80,pin81,w0,w1,
      SourceBoundaryIntervalReadout.slope4,
      SourceBoundarySignBounds.compactA,SourceBoundarySignBounds.compactB]
     nd_eval))

theorem num0_eq : numeratorBox 0=intv
    (-162113776073107683802206134891033287/9671406556917033397649408000000000000)
    (-802525480204520219927264718496741399/48357032784585166988247040000000000000) := by
  numerator_endpoint_eval
theorem num1_eq : numeratorBox 1=intv
    (-130807763171189710028216967987293329/9671406556917033397649408000000000000)
    (-161671784654471515528490494245672891/12089258196146291747061760000000000000) := by
  numerator_endpoint_eval
theorem num2_eq : numeratorBox 2=intv
    (-46844121548952902372015295207239481/2417851639229258349412352000000000000)
    (-932025347659384688181702124972096153/48357032784585166988247040000000000000) := by
  numerator_endpoint_eval
theorem num3_eq : numeratorBox 3=intv
    (-90039334674120153695032343894802657/4835703278458516698824704000000000000)
    (-89596044429384535912950009204530143/4835703278458516698824704000000000000) := by
  numerator_endpoint_eval
theorem num4_eq : numeratorBox 4=intv
    (-113237328134291914742932540022529543/19342813113834066795298816000000000000)
    (-557180420199788697022607250268195939/96714065569170333976494080000000000000) := by
  numerator_endpoint_eval

end N11Formalization.SourceStressGridReadout
#print axioms N11Formalization.SourceStressGridReadout.centralA_eq
#print axioms N11Formalization.SourceStressGridReadout.num4_eq
