import N11Formalization.SharedMomentConcreteFace1Data
import N11Formalization.SharedMomentEfficientFactorCertificate

/-! Class33 DRAFT (uncompiled): q0m2 face {1,2,9} canonical coefficients, plane tree,
568 leaves (exact Python pre-validation of every leaf, py/face_kernel.py). -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.Class33FaceTreeQ0M2F1_2_9
open RationalBoxSubdivision SharedMomentFacePlaneGradientCertificate SharedMomentFacePlaneCertificate
open SharedMomentFacePlaneDirectCertificate SharedMomentFactorRationalNodes
open SharedMomentFactorIntervalCertificate SharedMomentFactorLocalGradientCertificate
open RationalTrigLocalLipschitz SharedMomentConcreteFace1

def fc_p : Fin 3 → ℚ := ![(935783/31250000 : ℚ),(-40768173/500000000 : ℚ),(10358433/500000000 : ℚ)]
def fc_q : Fin 3 → ℚ := ![(-69002849/1000000000 : ℚ),(-31/6250000 : ℚ),(-40785971/200000000 : ℚ)]
def fc_b : Fin 3 → ℚ := ![(-26001207/200000000 : ℚ),(13/1600000 : ℚ),(1555963/5000000 : ℚ)]
def fc_bound : ℚ := (15769/125000 : ℚ)
def fc_leaf (B : Cell (Fin 2)) : Prop :=
  GradientPlaneLeaf fc_p fc_q fc_b fc_bound B

theorem node_0 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/16000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_2 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/16000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_0 node_1

theorem node_3 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (1571/8000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_4 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (4713/32000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_5 : Certificate fc_leaf
    (planeBox (4713/32000 : ℚ) (1571/8000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_6 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (1571/8000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/16000 : ℚ) (4713/32000 : ℚ) (1571/8000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_4 node_5

theorem node_7 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (1571/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_one (1571/16000 : ℚ) (1571/8000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_3 node_6

theorem node_8 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_2 node_7

theorem node_9 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/32000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_10 : Certificate fc_leaf
    (planeBox (1571/32000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_11 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (by norm_num) (by norm_num)
    node_9 node_10

theorem node_12 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/32000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_13 : Certificate fc_leaf
    (planeBox (1571/32000 : ℚ) (1571/16000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_14 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/16000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_12 node_13

theorem node_15 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_11 node_14

theorem node_16 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (4713/32000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_17 : Certificate fc_leaf
    (planeBox (4713/32000 : ℚ) (1571/8000 : ℚ) (1571/8000 : ℚ) (1571/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_18 : Certificate fc_leaf
    (planeBox (4713/32000 : ℚ) (1571/8000 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_19 : Certificate fc_leaf
    (planeBox (4713/32000 : ℚ) (1571/8000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  exact planeBox_split_one (4713/32000 : ℚ) (1571/8000 : ℚ) (1571/8000 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ) (by norm_num) (by norm_num)
    node_17 node_18

theorem node_20 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (1571/8000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/16000 : ℚ) (4713/32000 : ℚ) (1571/8000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (by norm_num) (by norm_num)
    node_16 node_19

theorem node_21 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (4713/32000 : ℚ) (4713/16000 : ℚ) (10997/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_22 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (4713/32000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_23 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (4713/32000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (1571/16000 : ℚ) (4713/32000 : ℚ) (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_21 node_22

theorem node_24 : Certificate fc_leaf
    (planeBox (4713/32000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (10997/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_25 : Certificate fc_leaf
    (planeBox (4713/32000 : ℚ) (1571/8000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_26 : Certificate fc_leaf
    (planeBox (4713/32000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (4713/32000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_24 node_25

theorem node_27 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/16000 : ℚ) (4713/32000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_23 node_26

theorem node_28 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (1571/8000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (1571/16000 : ℚ) (1571/8000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_20 node_27

theorem node_29 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_15 node_28

theorem node_30 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_8 node_29

theorem node_31 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_32 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/6400 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_33 : Certificate fc_leaf
    (planeBox (1571/6400 : ℚ) (4713/16000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_34 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_32 node_33

theorem node_35 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (4713/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_31 node_34

theorem node_36 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (10997/32000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_37 : Certificate fc_leaf
    (planeBox (10997/32000 : ℚ) (1571/4000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_38 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_zero (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_36 node_37

theorem node_39 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_40 : Certificate fc_leaf
    (planeBox (10997/32000 : ℚ) (1571/4000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_41 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_39 node_40

theorem node_42 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_one (4713/16000 : ℚ) (1571/4000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_38 node_41

theorem node_43 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_35 node_42

theorem node_44 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/6400 : ℚ) (1571/8000 : ℚ) (1571/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_45 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/6400 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_46 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/6400 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (1571/6400 : ℚ) (1571/8000 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ) (by norm_num) (by norm_num)
    node_44 node_45

theorem node_47 : Certificate fc_leaf
    (planeBox (1571/6400 : ℚ) (4713/16000 : ℚ) (1571/8000 : ℚ) (1571/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_48 : Certificate fc_leaf
    (planeBox (1571/6400 : ℚ) (4713/16000 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_49 : Certificate fc_leaf
    (planeBox (1571/6400 : ℚ) (4713/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  exact planeBox_split_one (1571/6400 : ℚ) (4713/16000 : ℚ) (1571/8000 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ) (by norm_num) (by norm_num)
    node_47 node_48

theorem node_50 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (by norm_num) (by norm_num)
    node_46 node_49

theorem node_51 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ) (10997/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_52 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/6400 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_53 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_51 node_52

theorem node_54 : Certificate fc_leaf
    (planeBox (1571/6400 : ℚ) (4713/16000 : ℚ) (4713/16000 : ℚ) (10997/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_55 : Certificate fc_leaf
    (planeBox (1571/6400 : ℚ) (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_56 : Certificate fc_leaf
    (planeBox (1571/6400 : ℚ) (4713/16000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (1571/6400 : ℚ) (4713/16000 : ℚ) (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_54 node_55

theorem node_57 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_53 node_56

theorem node_58 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_50 node_57

theorem node_59 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/8000 : ℚ) (1571/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_60 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_61 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  exact planeBox_split_one (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/8000 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ) (by norm_num) (by norm_num)
    node_59 node_60

theorem node_62 : Certificate fc_leaf
    (planeBox (10997/32000 : ℚ) (1571/4000 : ℚ) (1571/8000 : ℚ) (1571/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_63 : Certificate fc_leaf
    (planeBox (10997/32000 : ℚ) (1571/4000 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_64 : Certificate fc_leaf
    (planeBox (10997/32000 : ℚ) (1571/4000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  exact planeBox_split_one (10997/32000 : ℚ) (1571/4000 : ℚ) (1571/8000 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ) (by norm_num) (by norm_num)
    node_62 node_63

theorem node_65 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  exact planeBox_split_zero (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (by norm_num) (by norm_num)
    node_61 node_64

theorem node_66 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (10997/32000 : ℚ) (4713/16000 : ℚ) (10997/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_67 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (10997/32000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_68 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (10997/32000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (4713/16000 : ℚ) (10997/32000 : ℚ) (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_66 node_67

theorem node_69 : Certificate fc_leaf
    (planeBox (10997/32000 : ℚ) (1571/4000 : ℚ) (4713/16000 : ℚ) (10997/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_70 : Certificate fc_leaf
    (planeBox (10997/32000 : ℚ) (1571/4000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_71 : Certificate fc_leaf
    (planeBox (10997/32000 : ℚ) (1571/4000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (10997/32000 : ℚ) (1571/4000 : ℚ) (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_69 node_70

theorem node_72 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_68 node_71

theorem node_73 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_65 node_72

theorem node_74 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_58 node_73

theorem node_75 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (1571/4000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_43 node_74

theorem node_76 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_30 node_75

theorem node_77 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/32000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_78 : Certificate fc_leaf
    (planeBox (1571/32000 : ℚ) (1571/16000 : ℚ) (1571/4000 : ℚ) (14139/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_79 : Certificate fc_leaf
    (planeBox (1571/32000 : ℚ) (1571/16000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_80 : Certificate fc_leaf
    (planeBox (1571/32000 : ℚ) (1571/16000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  exact planeBox_split_one (1571/32000 : ℚ) (1571/16000 : ℚ) (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (by norm_num) (by norm_num)
    node_78 node_79

theorem node_81 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/16000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (by norm_num) (by norm_num)
    node_77 node_80

theorem node_82 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/32000 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_83 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/32000 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_84 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/32000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/32000 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_82 node_83

theorem node_85 : Certificate fc_leaf
    (planeBox (1571/32000 : ℚ) (1571/16000 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_86 : Certificate fc_leaf
    (planeBox (1571/32000 : ℚ) (1571/16000 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_87 : Certificate fc_leaf
    (planeBox (1571/32000 : ℚ) (1571/16000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (1571/32000 : ℚ) (1571/16000 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_85 node_86

theorem node_88 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/16000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_84 node_87

theorem node_89 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/16000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/16000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_81 node_88

theorem node_90 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (4713/32000 : ℚ) (1571/4000 : ℚ) (14139/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_91 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (4713/32000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_92 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (4713/32000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  exact planeBox_split_one (1571/16000 : ℚ) (4713/32000 : ℚ) (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (by norm_num) (by norm_num)
    node_90 node_91

theorem node_93 : Certificate fc_leaf
    (planeBox (4713/32000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (14139/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_94 : Certificate fc_leaf
    (planeBox (4713/32000 : ℚ) (1571/8000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_95 : Certificate fc_leaf
    (planeBox (4713/32000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  exact planeBox_split_one (4713/32000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (by norm_num) (by norm_num)
    node_93 node_94

theorem node_96 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  exact planeBox_split_zero (1571/16000 : ℚ) (4713/32000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (by norm_num) (by norm_num)
    node_92 node_95

theorem node_97 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (4713/32000 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_98 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (4713/32000 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_99 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (4713/32000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (1571/16000 : ℚ) (4713/32000 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_97 node_98

theorem node_100 : Certificate fc_leaf
    (planeBox (4713/32000 : ℚ) (1571/8000 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_101 : Certificate fc_leaf
    (planeBox (4713/32000 : ℚ) (1571/8000 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_102 : Certificate fc_leaf
    (planeBox (4713/32000 : ℚ) (1571/8000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (4713/32000 : ℚ) (1571/8000 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_100 node_101

theorem node_103 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (1571/8000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/16000 : ℚ) (4713/32000 : ℚ) (1571/8000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_99 node_102

theorem node_104 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (1571/16000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_96 node_103

theorem node_105 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_89 node_104

theorem node_106 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/32000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_107 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/32000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_108 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/32000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/32000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    node_106 node_107

theorem node_109 : Certificate fc_leaf
    (planeBox (1571/32000 : ℚ) (1571/16000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_110 : Certificate fc_leaf
    (planeBox (1571/32000 : ℚ) (1571/16000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_111 : Certificate fc_leaf
    (planeBox (1571/32000 : ℚ) (1571/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_one (1571/32000 : ℚ) (1571/16000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    node_109 node_110

theorem node_112 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    node_108 node_111

theorem node_113 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/32000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_114 : Certificate fc_leaf
    (planeBox (1571/32000 : ℚ) (1571/16000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_115 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/16000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_113 node_114

theorem node_116 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/16000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_112 node_115

theorem node_117 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (4713/32000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_118 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (4713/32000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_119 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (4713/32000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_one (1571/16000 : ℚ) (4713/32000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    node_117 node_118

theorem node_120 : Certificate fc_leaf
    (planeBox (4713/32000 : ℚ) (1571/8000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_121 : Certificate fc_leaf
    (planeBox (4713/32000 : ℚ) (1571/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_122 : Certificate fc_leaf
    (planeBox (4713/32000 : ℚ) (1571/8000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_one (4713/32000 : ℚ) (1571/8000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    node_120 node_121

theorem node_123 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (1571/8000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/16000 : ℚ) (4713/32000 : ℚ) (1571/8000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    node_119 node_122

theorem node_124 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (4713/32000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_125 : Certificate fc_leaf
    (planeBox (4713/32000 : ℚ) (1571/8000 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_126 : Certificate fc_leaf
    (planeBox (4713/32000 : ℚ) (1571/8000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_127 : Certificate fc_leaf
    (planeBox (4713/32000 : ℚ) (1571/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (4713/32000 : ℚ) (1571/8000 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_125 node_126

theorem node_128 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (1571/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/16000 : ℚ) (4713/32000 : ℚ) (1571/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_124 node_127

theorem node_129 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (1571/8000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/16000 : ℚ) (1571/8000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_123 node_128

theorem node_130 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_116 node_129

theorem node_131 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_105 node_130

theorem node_132 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/6400 : ℚ) (1571/4000 : ℚ) (14139/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_133 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/6400 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_134 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/6400 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (1571/6400 : ℚ) (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (by norm_num) (by norm_num)
    node_132 node_133

theorem node_135 : Certificate fc_leaf
    (planeBox (1571/6400 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (14139/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_136 : Certificate fc_leaf
    (planeBox (1571/6400 : ℚ) (17281/64000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_137 : Certificate fc_leaf
    (planeBox (17281/64000 : ℚ) (4713/16000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_138 : Certificate fc_leaf
    (planeBox (1571/6400 : ℚ) (4713/16000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ)) := by
  exact planeBox_split_zero (1571/6400 : ℚ) (17281/64000 : ℚ) (4713/16000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (by norm_num) (by norm_num)
    node_136 node_137

theorem node_139 : Certificate fc_leaf
    (planeBox (1571/6400 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  exact planeBox_split_one (1571/6400 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (by norm_num) (by norm_num)
    node_135 node_138

theorem node_140 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (by norm_num) (by norm_num)
    node_134 node_139

theorem node_141 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (14139/64000 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_142 : Certificate fc_leaf
    (planeBox (14139/64000 : ℚ) (1571/6400 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_143 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/6400 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (14139/64000 : ℚ) (1571/6400 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ) (by norm_num) (by norm_num)
    node_141 node_142

theorem node_144 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/6400 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_145 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/6400 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (1571/6400 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_143 node_144

theorem node_146 : Certificate fc_leaf
    (planeBox (1571/6400 : ℚ) (17281/64000 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_147 : Certificate fc_leaf
    (planeBox (17281/64000 : ℚ) (4713/16000 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_148 : Certificate fc_leaf
    (planeBox (1571/6400 : ℚ) (4713/16000 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ)) := by
  exact planeBox_split_zero (1571/6400 : ℚ) (17281/64000 : ℚ) (4713/16000 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ) (by norm_num) (by norm_num)
    node_146 node_147

theorem node_149 : Certificate fc_leaf
    (planeBox (1571/6400 : ℚ) (4713/16000 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_150 : Certificate fc_leaf
    (planeBox (1571/6400 : ℚ) (4713/16000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (1571/6400 : ℚ) (4713/16000 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_148 node_149

theorem node_151 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_145 node_150

theorem node_152 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_140 node_151

theorem node_153 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ) (14139/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_154 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (20423/64000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_155 : Certificate fc_leaf
    (planeBox (20423/64000 : ℚ) (10997/32000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_156 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (10997/32000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ)) := by
  exact planeBox_split_zero (4713/16000 : ℚ) (20423/64000 : ℚ) (10997/32000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (by norm_num) (by norm_num)
    node_154 node_155

theorem node_157 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  exact planeBox_split_one (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (by norm_num) (by norm_num)
    node_153 node_156

theorem node_158 : Certificate fc_leaf
    (planeBox (10997/32000 : ℚ) (1571/4000 : ℚ) (1571/4000 : ℚ) (14139/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_159 : Certificate fc_leaf
    (planeBox (10997/32000 : ℚ) (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_160 : Certificate fc_leaf
    (planeBox (10997/32000 : ℚ) (1571/4000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  exact planeBox_split_one (10997/32000 : ℚ) (1571/4000 : ℚ) (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (by norm_num) (by norm_num)
    node_158 node_159

theorem node_161 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  exact planeBox_split_zero (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (by norm_num) (by norm_num)
    node_157 node_160

theorem node_162 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_163 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (10997/32000 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_164 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_162 node_163

theorem node_165 : Certificate fc_leaf
    (planeBox (10997/32000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_166 : Certificate fc_leaf
    (planeBox (10997/32000 : ℚ) (1571/4000 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_167 : Certificate fc_leaf
    (planeBox (10997/32000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (10997/32000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_165 node_166

theorem node_168 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_164 node_167

theorem node_169 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_161 node_168

theorem node_170 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_152 node_169

theorem node_171 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/6400 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_172 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/6400 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_173 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/6400 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (1571/6400 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    node_171 node_172

theorem node_174 : Certificate fc_leaf
    (planeBox (1571/6400 : ℚ) (4713/16000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_175 : Certificate fc_leaf
    (planeBox (1571/6400 : ℚ) (4713/16000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_176 : Certificate fc_leaf
    (planeBox (1571/6400 : ℚ) (4713/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_one (1571/6400 : ℚ) (4713/16000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    node_174 node_175

theorem node_177 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    node_173 node_176

theorem node_178 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/6400 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_179 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/6400 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_180 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/6400 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (1571/6400 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_178 node_179

theorem node_181 : Certificate fc_leaf
    (planeBox (1571/6400 : ℚ) (4713/16000 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_182 : Certificate fc_leaf
    (planeBox (1571/6400 : ℚ) (4713/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_183 : Certificate fc_leaf
    (planeBox (1571/6400 : ℚ) (4713/16000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/6400 : ℚ) (4713/16000 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_181 node_182

theorem node_184 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_180 node_183

theorem node_185 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (4713/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_177 node_184

theorem node_186 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (10997/32000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_187 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (10997/32000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_188 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (10997/32000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_one (4713/16000 : ℚ) (10997/32000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    node_186 node_187

theorem node_189 : Certificate fc_leaf
    (planeBox (10997/32000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_190 : Certificate fc_leaf
    (planeBox (10997/32000 : ℚ) (1571/4000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_191 : Certificate fc_leaf
    (planeBox (10997/32000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_one (10997/32000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    node_189 node_190

theorem node_192 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_zero (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    node_188 node_191

theorem node_193 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (10997/32000 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_194 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (10997/32000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_195 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (10997/32000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (4713/16000 : ℚ) (10997/32000 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_193 node_194

theorem node_196 : Certificate fc_leaf
    (planeBox (10997/32000 : ℚ) (1571/4000 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_197 : Certificate fc_leaf
    (planeBox (10997/32000 : ℚ) (1571/4000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_198 : Certificate fc_leaf
    (planeBox (10997/32000 : ℚ) (1571/4000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (10997/32000 : ℚ) (1571/4000 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_196 node_197

theorem node_199 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_195 node_198

theorem node_200 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (4713/16000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_192 node_199

theorem node_201 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_185 node_200

theorem node_202 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_170 node_201

theorem node_203 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_131 node_202

theorem node_204 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/4000 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_76 node_203

theorem node_205 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_206 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_207 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_205 node_206

theorem node_208 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_209 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_210 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_208 node_209

theorem node_211 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (1571/3200 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_207 node_210

theorem node_212 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_213 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_214 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_212 node_213

theorem node_215 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_216 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_217 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_215 node_216

theorem node_218 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_one (1571/3200 : ℚ) (4713/8000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_214 node_217

theorem node_219 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_211 node_218

theorem node_220 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/8000 : ℚ) (1571/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_221 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_222 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/8000 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ) (by norm_num) (by norm_num)
    node_220 node_221

theorem node_223 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (1571/8000 : ℚ) (1571/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_224 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_225 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  exact planeBox_split_one (14139/32000 : ℚ) (1571/3200 : ℚ) (1571/8000 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ) (by norm_num) (by norm_num)
    node_223 node_224

theorem node_226 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (by norm_num) (by norm_num)
    node_222 node_225

theorem node_227 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (4713/16000 : ℚ) (10997/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_228 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_229 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (14139/32000 : ℚ) (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_227 node_228

theorem node_230 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (4713/16000 : ℚ) (10997/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_231 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_232 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (14139/32000 : ℚ) (1571/3200 : ℚ) (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_230 node_231

theorem node_233 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_229 node_232

theorem node_234 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (1571/3200 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_226 node_233

theorem node_235 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_236 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_237 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (by norm_num) (by norm_num)
    node_235 node_236

theorem node_238 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/16000 : ℚ) (10997/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_239 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_240 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_238 node_239

theorem node_241 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_242 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_240 node_241

theorem node_243 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_237 node_242

theorem node_244 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_234 node_243

theorem node_245 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (4713/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_219 node_244

theorem node_246 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_247 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_248 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_246 node_247

theorem node_249 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_250 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_251 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_249 node_250

theorem node_252 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (10997/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_248 node_251

theorem node_253 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_254 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_255 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_253 node_254

theorem node_256 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_257 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_258 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_256 node_257

theorem node_259 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_255 node_258

theorem node_260 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_252 node_259

theorem node_261 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_262 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_263 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (by norm_num) (by norm_num)
    node_261 node_262

theorem node_264 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_265 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_266 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_264 node_265

theorem node_267 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_263 node_266

theorem node_268 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_269 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_270 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (by norm_num) (by norm_num)
    node_268 node_269

theorem node_271 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_272 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_273 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_271 node_272

theorem node_274 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_270 node_273

theorem node_275 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_267 node_274

theorem node_276 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_260 node_275

theorem node_277 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_245 node_276

theorem node_278 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/4000 : ℚ) (14139/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_279 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_280 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (by norm_num) (by norm_num)
    node_278 node_279

theorem node_281 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (1571/4000 : ℚ) (14139/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_282 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_283 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  exact planeBox_split_one (14139/32000 : ℚ) (1571/3200 : ℚ) (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (by norm_num) (by norm_num)
    node_281 node_282

theorem node_284 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (by norm_num) (by norm_num)
    node_280 node_283

theorem node_285 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_286 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_287 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_285 node_286

theorem node_288 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_289 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_290 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (14139/32000 : ℚ) (1571/3200 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_288 node_289

theorem node_291 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_287 node_290

theorem node_292 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (1571/3200 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_284 node_291

theorem node_293 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (1571/4000 : ℚ) (14139/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_294 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_295 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  exact planeBox_split_one (1571/3200 : ℚ) (17281/32000 : ℚ) (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (by norm_num) (by norm_num)
    node_293 node_294

theorem node_296 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_297 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  exact planeBox_split_zero (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (by norm_num) (by norm_num)
    node_295 node_296

theorem node_298 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_299 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_300 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (1571/3200 : ℚ) (17281/32000 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_298 node_299

theorem node_301 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_302 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_303 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (17281/32000 : ℚ) (4713/8000 : ℚ) (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_301 node_302

theorem node_304 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_300 node_303

theorem node_305 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_297 node_304

theorem node_306 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_292 node_305

theorem node_307 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_308 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_309 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (14139/32000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    node_307 node_308

theorem node_310 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_311 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_312 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_one (14139/32000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    node_310 node_311

theorem node_313 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    node_309 node_312

theorem node_314 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_315 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_316 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (14139/32000 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_314 node_315

theorem node_317 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_318 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_319 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (14139/32000 : ℚ) (1571/3200 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_317 node_318

theorem node_320 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_316 node_319

theorem node_321 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_313 node_320

theorem node_322 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_323 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_324 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_one (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    node_322 node_323

theorem node_325 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_326 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_327 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_one (17281/32000 : ℚ) (4713/8000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    node_325 node_326

theorem node_328 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    node_324 node_327

theorem node_329 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_330 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_331 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/3200 : ℚ) (17281/32000 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_329 node_330

theorem node_332 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_333 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_334 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (17281/32000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_332 node_333

theorem node_335 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_331 node_334

theorem node_336 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/3200 : ℚ) (4713/8000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_328 node_335

theorem node_337 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_321 node_336

theorem node_338 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_306 node_337

theorem node_339 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_340 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_341 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (by norm_num) (by norm_num)
    node_339 node_340

theorem node_342 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_343 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_344 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_342 node_343

theorem node_345 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_341 node_344

theorem node_346 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_347 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_348 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (by norm_num) (by norm_num)
    node_346 node_347

theorem node_349 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_350 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_351 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_349 node_350

theorem node_352 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_348 node_351

theorem node_353 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_345 node_352

theorem node_354 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_355 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_356 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    node_354 node_355

theorem node_357 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_358 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_359 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_357 node_358

theorem node_360 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (10997/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_356 node_359

theorem node_361 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_362 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_363 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    node_361 node_362

theorem node_364 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_365 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_366 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_364 node_365

theorem node_367 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_363 node_366

theorem node_368 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_360 node_367

theorem node_369 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_353 node_368

theorem node_370 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_338 node_369

theorem node_371 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_277 node_370

theorem node_372 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_204 node_371

theorem node_373 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/32000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_374 : Certificate fc_leaf
    (planeBox (1571/32000 : ℚ) (1571/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_375 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    node_373 node_374

theorem node_376 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/16000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_377 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/16000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_375 node_376

theorem node_378 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (4713/32000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_379 : Certificate fc_leaf
    (planeBox (4713/32000 : ℚ) (1571/8000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_380 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (1571/8000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/16000 : ℚ) (4713/32000 : ℚ) (1571/8000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    node_378 node_379

theorem node_381 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (1571/8000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_382 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (1571/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (1571/16000 : ℚ) (1571/8000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_380 node_381

theorem node_383 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_377 node_382

theorem node_384 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_385 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (1571/8000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_386 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_384 node_385

theorem node_387 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_383 node_386

theorem node_388 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/6400 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_389 : Certificate fc_leaf
    (planeBox (1571/6400 : ℚ) (4713/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_390 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    node_388 node_389

theorem node_391 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/6400 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_392 : Certificate fc_leaf
    (planeBox (1571/6400 : ℚ) (4713/16000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_393 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_391 node_392

theorem node_394 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_390 node_393

theorem node_395 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_396 : Certificate fc_leaf
    (planeBox (10997/32000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_397 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_zero (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    node_395 node_396

theorem node_398 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (10997/32000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_399 : Certificate fc_leaf
    (planeBox (10997/32000 : ℚ) (1571/4000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_400 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_398 node_399

theorem node_401 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_397 node_400

theorem node_402 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_394 node_401

theorem node_403 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_404 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_405 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_403 node_404

theorem node_406 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_407 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_408 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_406 node_407

theorem node_409 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_405 node_408

theorem node_410 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_402 node_409

theorem node_411 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_387 node_410

theorem node_412 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_413 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_414 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_412 node_413

theorem node_415 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_416 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_417 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_415 node_416

theorem node_418 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_419 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_420 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_418 node_419

theorem node_421 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (1571/4000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_417 node_420

theorem node_422 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_414 node_421

theorem node_423 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_411 node_422

theorem node_424 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_425 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_426 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    node_424 node_425

theorem node_427 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_428 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_429 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_427 node_428

theorem node_430 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (1571/3200 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_426 node_429

theorem node_431 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_432 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_433 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    node_431 node_432

theorem node_434 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_435 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_436 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_434 node_435

theorem node_437 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_433 node_436

theorem node_438 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_430 node_437

theorem node_439 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_440 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_441 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    node_439 node_440

theorem node_442 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_443 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (1571/3200 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_441 node_442

theorem node_444 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_445 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_446 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    node_444 node_445

theorem node_447 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_448 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_449 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_447 node_448

theorem node_450 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_446 node_449

theorem node_451 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_443 node_450

theorem node_452 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_438 node_451

theorem node_453 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_454 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_455 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (20423/32000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    node_453 node_454

theorem node_456 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_457 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_458 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_one (20423/32000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    node_456 node_457

theorem node_459 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    node_455 node_458

theorem node_460 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_461 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_462 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (20423/32000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_460 node_461

theorem node_463 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_464 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_465 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (20423/32000 : ℚ) (10997/16000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_463 node_464

theorem node_466 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_462 node_465

theorem node_467 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_459 node_466

theorem node_468 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_469 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_470 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    node_468 node_469

theorem node_471 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_472 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_473 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_one (4713/6400 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    node_471 node_472

theorem node_474 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    node_470 node_473

theorem node_475 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_476 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_477 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (4713/6400 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_475 node_476

theorem node_478 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_479 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_480 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (4713/6400 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_478 node_479

theorem node_481 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_477 node_480

theorem node_482 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_474 node_481

theorem node_483 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_467 node_482

theorem node_484 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_485 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_486 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_487 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_one (20423/32000 : ℚ) (10997/16000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    node_485 node_486

theorem node_488 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    node_484 node_487

theorem node_489 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_490 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_491 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_489 node_490

theorem node_492 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_488 node_491

theorem node_493 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_494 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_495 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    node_493 node_494

theorem node_496 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_497 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_498 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_one (4713/6400 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    node_496 node_497

theorem node_499 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    node_495 node_498

theorem node_500 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_501 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_502 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (4713/6400 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_500 node_501

theorem node_503 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_504 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_505 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (4713/6400 : ℚ) (1571/2000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_503 node_504

theorem node_506 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_502 node_505

theorem node_507 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_499 node_506

theorem node_508 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_492 node_507

theorem node_509 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_483 node_508

theorem node_510 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_452 node_509

theorem node_511 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_512 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_513 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_511 node_512

theorem node_514 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_515 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_516 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (1571/3200 : ℚ) (4713/8000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_514 node_515

theorem node_517 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_513 node_516

theorem node_518 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_519 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_520 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_518 node_519

theorem node_521 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (4713/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_517 node_520

theorem node_522 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_523 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_524 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (by norm_num) (by norm_num)
    node_522 node_523

theorem node_525 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_526 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (10997/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_524 node_525

theorem node_527 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_528 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_529 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (by norm_num) (by norm_num)
    node_527 node_528

theorem node_530 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_531 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_529 node_530

theorem node_532 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_526 node_531

theorem node_533 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_534 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_535 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (10997/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_533 node_534

theorem node_536 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_537 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_538 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (1571/2000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_536 node_537

theorem node_539 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_535 node_538

theorem node_540 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_532 node_539

theorem node_541 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_521 node_540

theorem node_542 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_510 node_541

theorem node_543 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_423 node_542

theorem node_544 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_372 node_543

theorem node_545 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_546 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_547 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_545 node_546

theorem node_548 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_549 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_550 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_548 node_549

theorem node_551 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (14139/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_547 node_550

theorem node_552 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_553 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_554 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (1571/1600 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_552 node_553

theorem node_555 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_551 node_554

theorem node_556 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_557 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_558 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (by norm_num) (by norm_num)
    node_556 node_557

theorem node_559 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_560 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_561 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_559 node_560

theorem node_562 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_558 node_561

theorem node_563 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_564 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_565 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (by norm_num) (by norm_num)
    node_563 node_564

theorem node_566 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_567 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_565 node_566

theorem node_568 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_562 node_567

theorem node_569 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (1571/1600 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_555 node_568

theorem node_570 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_571 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_572 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (17281/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_570 node_571

theorem node_573 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_574 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_575 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (4713/4000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_573 node_574

theorem node_576 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_572 node_575

theorem node_577 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_578 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_579 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_577 node_578

theorem node_580 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_581 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_582 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_580 node_581

theorem node_583 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_579 node_582

theorem node_584 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (4713/4000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_576 node_583

theorem node_585 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (4713/4000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_569 node_584

theorem node_586 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_587 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_588 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_586 node_587

theorem node_589 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_590 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_591 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_589 node_590

theorem node_592 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_588 node_591

theorem node_593 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_594 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_595 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_596 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_594 node_595

theorem node_597 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (14139/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_593 node_596

theorem node_598 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_599 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_600 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_601 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_599 node_600

theorem node_602 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_598 node_601

theorem node_603 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_597 node_602

theorem node_604 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_592 node_603

theorem node_605 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_606 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_607 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_605 node_606

theorem node_608 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_609 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_610 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_608 node_609

theorem node_611 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_607 node_610

theorem node_612 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_613 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_614 : Certificate fc_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_615 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_613 node_614

theorem node_616 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_612 node_615

theorem node_617 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_618 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_619 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (4713/4000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_617 node_618

theorem node_620 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_616 node_619

theorem node_621 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_611 node_620

theorem node_622 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_604 node_621

theorem node_623 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (4713/4000 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (4713/4000 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_585 node_622

theorem node_624 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_625 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_626 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_624 node_625

theorem node_627 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_628 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_629 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (20423/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_627 node_628

theorem node_630 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_631 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_632 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_630 node_631

theorem node_633 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_629 node_632

theorem node_634 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (10997/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_626 node_633

theorem node_635 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_636 : Certificate fc_leaf
    (planeBox (4713/3200 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_637 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_635 node_636

theorem node_638 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_639 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_640 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_638 node_639

theorem node_641 : Certificate fc_leaf
    (planeBox (4713/3200 : ℚ) (1571/1000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_642 : Certificate fc_leaf
    (planeBox (4713/3200 : ℚ) (1571/1000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_643 : Certificate fc_leaf
    (planeBox (4713/3200 : ℚ) (1571/1000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (4713/3200 : ℚ) (1571/1000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_641 node_642

theorem node_644 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_640 node_643

theorem node_645 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (10997/8000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_637 node_644

theorem node_646 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_634 node_645

theorem node_647 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_648 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_649 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (20423/16000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_647 node_648

theorem node_650 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_651 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_652 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_650 node_651

theorem node_653 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_649 node_652

theorem node_654 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_655 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_656 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (20423/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_654 node_655

theorem node_657 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_658 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_659 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (20423/16000 : ℚ) (10997/8000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_657 node_658

theorem node_660 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_656 node_659

theorem node_661 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_653 node_660

theorem node_662 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_663 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_664 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_662 node_663

theorem node_665 : Certificate fc_leaf
    (planeBox (4713/3200 : ℚ) (1571/1000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_666 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_664 node_665

theorem node_667 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_668 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_669 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (10997/8000 : ℚ) (4713/3200 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_667 node_668

theorem node_670 : Certificate fc_leaf
    (planeBox (4713/3200 : ℚ) (1571/1000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_671 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_669 node_670

theorem node_672 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_666 node_671

theorem node_673 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_661 node_672

theorem node_674 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_646 node_673

theorem node_675 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_623 node_674

theorem node_676 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_677 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_678 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (26707/32000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    node_676 node_677

theorem node_679 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_680 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_681 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_one (26707/32000 : ℚ) (14139/16000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    node_679 node_680

theorem node_682 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    node_678 node_681

theorem node_683 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_684 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_685 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_683 node_684

theorem node_686 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_687 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_688 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (26707/32000 : ℚ) (14139/16000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_686 node_687

theorem node_689 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_685 node_688

theorem node_690 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_682 node_689

theorem node_691 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_692 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_693 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    node_691 node_692

theorem node_694 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_695 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_696 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_one (29849/32000 : ℚ) (1571/1600 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    node_694 node_695

theorem node_697 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    node_693 node_696

theorem node_698 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_699 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_700 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (29849/32000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_698 node_699

theorem node_701 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_702 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_703 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (29849/32000 : ℚ) (1571/1600 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_701 node_702

theorem node_704 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_700 node_703

theorem node_705 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_697 node_704

theorem node_706 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_690 node_705

theorem node_707 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_708 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_709 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (26707/32000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    node_707 node_708

theorem node_710 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_711 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_712 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_one (26707/32000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    node_710 node_711

theorem node_713 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    node_709 node_712

theorem node_714 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_715 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_716 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (26707/32000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_714 node_715

theorem node_717 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_718 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_719 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (26707/32000 : ℚ) (14139/16000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_717 node_718

theorem node_720 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_716 node_719

theorem node_721 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_713 node_720

theorem node_722 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_723 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_724 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    node_722 node_723

theorem node_725 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_726 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_727 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_one (29849/32000 : ℚ) (1571/1600 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    node_725 node_726

theorem node_728 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    node_724 node_727

theorem node_729 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_730 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_731 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (29849/32000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_729 node_730

theorem node_732 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_733 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_731 node_732

theorem node_734 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_728 node_733

theorem node_735 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_721 node_734

theorem node_736 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_706 node_735

theorem node_737 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_738 : Certificate fc_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_739 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    node_737 node_738

theorem node_740 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_741 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_742 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (32991/32000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_740 node_741

theorem node_743 : Certificate fc_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_744 : Certificate fc_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_745 : Certificate fc_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (32991/32000 : ℚ) (17281/16000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_743 node_744

theorem node_746 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_742 node_745

theorem node_747 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_739 node_746

theorem node_748 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_749 : Certificate fc_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_750 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    node_748 node_749

theorem node_751 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_752 : Certificate fc_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_753 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_751 node_752

theorem node_754 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_750 node_753

theorem node_755 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_747 node_754

theorem node_756 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_757 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_758 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (32991/32000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    node_756 node_757

theorem node_759 : Certificate fc_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_760 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    node_758 node_759

theorem node_761 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_762 : Certificate fc_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_763 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_761 node_762

theorem node_764 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_760 node_763

theorem node_765 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_766 : Certificate fc_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_767 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    node_765 node_766

theorem node_768 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_769 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_767 node_768

theorem node_770 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_764 node_769

theorem node_771 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_755 node_770

theorem node_772 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_736 node_771

theorem node_773 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_774 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_775 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (by norm_num) (by norm_num)
    node_773 node_774

theorem node_776 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_777 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (14139/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_775 node_776

theorem node_778 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_779 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_780 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (by norm_num) (by norm_num)
    node_778 node_779

theorem node_781 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_782 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_780 node_781

theorem node_783 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_777 node_782

theorem node_784 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_785 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_786 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_784 node_785

theorem node_787 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_783 node_786

theorem node_788 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_789 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_790 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_788 node_789

theorem node_791 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_792 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_793 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_791 node_792

theorem node_794 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_790 node_793

theorem node_795 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_796 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_794 node_795

theorem node_797 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_787 node_796

theorem node_798 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_772 node_797

theorem node_799 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_800 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_801 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (20423/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_799 node_800

theorem node_802 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_803 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_804 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_802 node_803

theorem node_805 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_801 node_804

theorem node_806 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_807 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_808 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (20423/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_806 node_807

theorem node_809 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_810 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_811 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_809 node_810

theorem node_812 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_808 node_811

theorem node_813 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_805 node_812

theorem node_814 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_815 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_816 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_814 node_815

theorem node_817 : Certificate fc_leaf
    (planeBox (4713/3200 : ℚ) (1571/1000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_818 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_816 node_817

theorem node_819 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_820 : Certificate fc_leaf
    (planeBox (4713/3200 : ℚ) (1571/1000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_821 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_819 node_820

theorem node_822 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_818 node_821

theorem node_823 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_813 node_822

theorem node_824 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_825 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_826 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_824 node_825

theorem node_827 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_828 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (10997/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_826 node_827

theorem node_829 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_830 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_831 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (10997/8000 : ℚ) (1571/1000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_829 node_830

theorem node_832 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (1571/1000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_828 node_831

theorem node_833 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_823 node_832

theorem node_834 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_798 node_833

theorem node_835 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_675 node_834

theorem node_836 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_544 node_835

theorem node_837 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_838 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_839 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/8000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_837 node_838

theorem node_840 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_841 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_842 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_840 node_841

theorem node_843 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_839 node_842

theorem node_844 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_845 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_846 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_844 node_845

theorem node_847 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (1571/1000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/4000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_843 node_846

theorem node_848 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_849 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_850 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ) (by norm_num) (by norm_num)
    node_848 node_849

theorem node_851 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_852 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_850 node_851

theorem node_853 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_854 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_855 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ) (by norm_num) (by norm_num)
    node_853 node_854

theorem node_856 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_857 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_855 node_856

theorem node_858 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_852 node_857

theorem node_859 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_860 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_861 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_859 node_860

theorem node_862 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_858 node_861

theorem node_863 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_847 node_862

theorem node_864 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (4713/2000 : ℚ) (10997/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_865 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (10997/4000 : ℚ) (1571/500 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_866 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (4713/2000 : ℚ) (1571/500 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/4000 : ℚ) (4713/2000 : ℚ) (10997/4000 : ℚ) (1571/500 : ℚ) (by norm_num) (by norm_num)
    node_864 node_865

theorem node_867 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (4713/2000 : ℚ) (1571/500 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_868 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/2000 : ℚ) (4713/2000 : ℚ) (1571/500 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (4713/2000 : ℚ) (1571/500 : ℚ) (by norm_num) (by norm_num)
    node_866 node_867

theorem node_869 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (1571/500 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (4713/2000 : ℚ) (1571/500 : ℚ) (by norm_num) (by norm_num)
    node_863 node_868

theorem node_870 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_871 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_872 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_870 node_871

theorem node_873 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_874 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_872 node_873

theorem node_875 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_876 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_874 node_875

theorem node_877 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/1000 : ℚ) (4713/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_878 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1000 : ℚ) (1571/1000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/1000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_876 node_877

theorem node_879 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1000 : ℚ) (4713/2000 : ℚ) (1571/500 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_880 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1000 : ℚ) (1571/1000 : ℚ) (1571/500 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (1571/1000 : ℚ) (1571/1000 : ℚ) (4713/2000 : ℚ) (1571/500 : ℚ) (by norm_num) (by norm_num)
    node_878 node_879

theorem node_881 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/1000 : ℚ) (1571/1000 : ℚ) (1571/500 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (1571/1000 : ℚ) (1571/500 : ℚ) (by norm_num) (by norm_num)
    node_869 node_880

theorem node_882 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/500 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/1000 : ℚ) (1571/500 : ℚ) (by norm_num) (by norm_num)
    node_836 node_881

theorem node_883 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (26707/16000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_884 : Certificate fc_leaf
    (planeBox (26707/16000 : ℚ) (14139/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_885 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (14139/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/1000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_883 node_884

theorem node_886 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (26707/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_887 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (26707/16000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_888 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (26707/16000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (1571/1000 : ℚ) (26707/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_886 node_887

theorem node_889 : Certificate fc_leaf
    (planeBox (26707/16000 : ℚ) (14139/8000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_890 : Certificate fc_leaf
    (planeBox (26707/16000 : ℚ) (14139/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_891 : Certificate fc_leaf
    (planeBox (26707/16000 : ℚ) (14139/8000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (26707/16000 : ℚ) (14139/8000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_889 node_890

theorem node_892 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/1000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_888 node_891

theorem node_893 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (14139/8000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (1571/1000 : ℚ) (14139/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_885 node_892

theorem node_894 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (29849/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_895 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (29849/16000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_896 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (29849/16000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_one (14139/8000 : ℚ) (29849/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_894 node_895

theorem node_897 : Certificate fc_leaf
    (planeBox (29849/16000 : ℚ) (1571/800 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_898 : Certificate fc_leaf
    (planeBox (29849/16000 : ℚ) (1571/800 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_899 : Certificate fc_leaf
    (planeBox (29849/16000 : ℚ) (1571/800 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_one (29849/16000 : ℚ) (1571/800 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_897 node_898

theorem node_900 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (1571/800 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (14139/8000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_896 node_899

theorem node_901 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (29849/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_902 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (29849/16000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_903 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (29849/16000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (14139/8000 : ℚ) (29849/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_901 node_902

theorem node_904 : Certificate fc_leaf
    (planeBox (29849/16000 : ℚ) (1571/800 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_905 : Certificate fc_leaf
    (planeBox (29849/16000 : ℚ) (1571/800 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_906 : Certificate fc_leaf
    (planeBox (29849/16000 : ℚ) (1571/800 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (29849/16000 : ℚ) (1571/800 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_904 node_905

theorem node_907 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (1571/800 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (14139/8000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_903 node_906

theorem node_908 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (1571/800 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (14139/8000 : ℚ) (1571/800 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_900 node_907

theorem node_909 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (1571/800 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_893 node_908

theorem node_910 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (26707/16000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_911 : Certificate fc_leaf
    (planeBox (26707/16000 : ℚ) (14139/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_912 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/1000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_910 node_911

theorem node_913 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (26707/16000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_914 : Certificate fc_leaf
    (planeBox (26707/16000 : ℚ) (14139/8000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_915 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (14139/8000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/1000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_913 node_914

theorem node_916 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_912 node_915

theorem node_917 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (29849/16000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_918 : Certificate fc_leaf
    (planeBox (29849/16000 : ℚ) (1571/800 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_919 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (1571/800 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (14139/8000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_917 node_918

theorem node_920 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (29849/16000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_921 : Certificate fc_leaf
    (planeBox (29849/16000 : ℚ) (1571/800 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_922 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (1571/800 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (14139/8000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_920 node_921

theorem node_923 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (1571/800 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (14139/8000 : ℚ) (1571/800 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_919 node_922

theorem node_924 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (1571/800 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_916 node_923

theorem node_925 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (1571/800 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/1000 : ℚ) (1571/800 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_909 node_924

theorem node_926 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (32991/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_927 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (32991/16000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_928 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (32991/16000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_one (1571/800 : ℚ) (32991/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_926 node_927

theorem node_929 : Certificate fc_leaf
    (planeBox (32991/16000 : ℚ) (67553/32000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_930 : Certificate fc_leaf
    (planeBox (67553/32000 : ℚ) (17281/8000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_931 : Certificate fc_leaf
    (planeBox (32991/16000 : ℚ) (17281/8000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_zero (32991/16000 : ℚ) (67553/32000 : ℚ) (17281/8000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_929 node_930

theorem node_932 : Certificate fc_leaf
    (planeBox (32991/16000 : ℚ) (67553/32000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_933 : Certificate fc_leaf
    (planeBox (67553/32000 : ℚ) (17281/8000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_934 : Certificate fc_leaf
    (planeBox (32991/16000 : ℚ) (17281/8000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (32991/16000 : ℚ) (67553/32000 : ℚ) (17281/8000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_932 node_933

theorem node_935 : Certificate fc_leaf
    (planeBox (32991/16000 : ℚ) (17281/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_one (32991/16000 : ℚ) (17281/8000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_931 node_934

theorem node_936 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (17281/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/800 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_928 node_935

theorem node_937 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (32991/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_938 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (32991/16000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_939 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (32991/16000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (1571/800 : ℚ) (32991/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_937 node_938

theorem node_940 : Certificate fc_leaf
    (planeBox (32991/16000 : ℚ) (17281/8000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_941 : Certificate fc_leaf
    (planeBox (32991/16000 : ℚ) (17281/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_942 : Certificate fc_leaf
    (planeBox (32991/16000 : ℚ) (17281/8000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (32991/16000 : ℚ) (17281/8000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_940 node_941

theorem node_943 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (17281/8000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/800 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_939 node_942

theorem node_944 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (17281/8000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (1571/800 : ℚ) (17281/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_936 node_943

theorem node_945 : Certificate fc_leaf
    (planeBox (17281/8000 : ℚ) (14139/6400 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_946 : Certificate fc_leaf
    (planeBox (14139/6400 : ℚ) (36133/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_947 : Certificate fc_leaf
    (planeBox (17281/8000 : ℚ) (36133/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_zero (17281/8000 : ℚ) (14139/6400 : ℚ) (36133/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_945 node_946

theorem node_948 : Certificate fc_leaf
    (planeBox (17281/8000 : ℚ) (14139/6400 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_949 : Certificate fc_leaf
    (planeBox (14139/6400 : ℚ) (36133/16000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_950 : Certificate fc_leaf
    (planeBox (17281/8000 : ℚ) (36133/16000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (17281/8000 : ℚ) (14139/6400 : ℚ) (36133/16000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_948 node_949

theorem node_951 : Certificate fc_leaf
    (planeBox (17281/8000 : ℚ) (36133/16000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_one (17281/8000 : ℚ) (36133/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_947 node_950

theorem node_952 : Certificate fc_leaf
    (planeBox (36133/16000 : ℚ) (73837/32000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_953 : Certificate fc_leaf
    (planeBox (36133/16000 : ℚ) (73837/32000 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_954 : Certificate fc_leaf
    (planeBox (36133/16000 : ℚ) (73837/32000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_one (36133/16000 : ℚ) (73837/32000 : ℚ) (0 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_952 node_953

theorem node_955 : Certificate fc_leaf
    (planeBox (73837/32000 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_956 : Certificate fc_leaf
    (planeBox (73837/32000 : ℚ) (4713/2000 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_957 : Certificate fc_leaf
    (planeBox (73837/32000 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_one (73837/32000 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_955 node_956

theorem node_958 : Certificate fc_leaf
    (planeBox (36133/16000 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_zero (36133/16000 : ℚ) (73837/32000 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_954 node_957

theorem node_959 : Certificate fc_leaf
    (planeBox (36133/16000 : ℚ) (73837/32000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_960 : Certificate fc_leaf
    (planeBox (73837/32000 : ℚ) (4713/2000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_961 : Certificate fc_leaf
    (planeBox (36133/16000 : ℚ) (4713/2000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (36133/16000 : ℚ) (73837/32000 : ℚ) (4713/2000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_959 node_960

theorem node_962 : Certificate fc_leaf
    (planeBox (36133/16000 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_one (36133/16000 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_958 node_961

theorem node_963 : Certificate fc_leaf
    (planeBox (17281/8000 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (17281/8000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_951 node_962

theorem node_964 : Certificate fc_leaf
    (planeBox (17281/8000 : ℚ) (36133/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_965 : Certificate fc_leaf
    (planeBox (17281/8000 : ℚ) (36133/16000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_966 : Certificate fc_leaf
    (planeBox (17281/8000 : ℚ) (36133/16000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (17281/8000 : ℚ) (36133/16000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_964 node_965

theorem node_967 : Certificate fc_leaf
    (planeBox (36133/16000 : ℚ) (4713/2000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_968 : Certificate fc_leaf
    (planeBox (36133/16000 : ℚ) (4713/2000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_969 : Certificate fc_leaf
    (planeBox (36133/16000 : ℚ) (4713/2000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (36133/16000 : ℚ) (4713/2000 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_967 node_968

theorem node_970 : Certificate fc_leaf
    (planeBox (17281/8000 : ℚ) (4713/2000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (17281/8000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_966 node_969

theorem node_971 : Certificate fc_leaf
    (planeBox (17281/8000 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (17281/8000 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_963 node_970

theorem node_972 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/800 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_944 node_971

theorem node_973 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (32991/16000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_974 : Certificate fc_leaf
    (planeBox (32991/16000 : ℚ) (17281/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_975 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (17281/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/800 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_973 node_974

theorem node_976 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (17281/8000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_977 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (17281/8000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/800 : ℚ) (17281/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_975 node_976

theorem node_978 : Certificate fc_leaf
    (planeBox (17281/8000 : ℚ) (36133/16000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_979 : Certificate fc_leaf
    (planeBox (36133/16000 : ℚ) (4713/2000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_980 : Certificate fc_leaf
    (planeBox (17281/8000 : ℚ) (4713/2000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (17281/8000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_978 node_979

theorem node_981 : Certificate fc_leaf
    (planeBox (17281/8000 : ℚ) (4713/2000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_982 : Certificate fc_leaf
    (planeBox (17281/8000 : ℚ) (4713/2000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (17281/8000 : ℚ) (4713/2000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_980 node_981

theorem node_983 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (4713/2000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/800 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_977 node_982

theorem node_984 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/800 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_972 node_983

theorem node_985 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/1000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_925 node_984

theorem node_986 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (26707/16000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_987 : Certificate fc_leaf
    (planeBox (26707/16000 : ℚ) (14139/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_988 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (1571/1000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_986 node_987

theorem node_989 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_990 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_988 node_989

theorem node_991 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (1571/800 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_992 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (1571/800 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_993 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (1571/800 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (14139/8000 : ℚ) (1571/800 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_991 node_992

theorem node_994 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (1571/800 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_990 node_993

theorem node_995 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (1571/800 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_996 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (1571/800 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/1000 : ℚ) (1571/800 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_994 node_995

theorem node_997 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (17281/8000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_998 : Certificate fc_leaf
    (planeBox (17281/8000 : ℚ) (4713/2000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_999 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (4713/2000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/800 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_997 node_998

theorem node_1000 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (4713/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_1001 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (4713/2000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/800 : ℚ) (4713/2000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_999 node_1000

theorem node_1002 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (4713/2000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (1571/1000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_996 node_1001

theorem node_1003 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/1000 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_985 node_1002

theorem node_1004 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (76979/32000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1005 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (76979/32000 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1006 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (76979/32000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_one (4713/2000 : ℚ) (76979/32000 : ℚ) (0 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_1004 node_1005

theorem node_1007 : Certificate fc_leaf
    (planeBox (76979/32000 : ℚ) (1571/640 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1008 : Certificate fc_leaf
    (planeBox (76979/32000 : ℚ) (1571/640 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1009 : Certificate fc_leaf
    (planeBox (76979/32000 : ℚ) (1571/640 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_one (76979/32000 : ℚ) (1571/640 : ℚ) (0 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_1007 node_1008

theorem node_1010 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (1571/640 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_zero (4713/2000 : ℚ) (76979/32000 : ℚ) (1571/640 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_1006 node_1009

theorem node_1011 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (76979/32000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1012 : Certificate fc_leaf
    (planeBox (76979/32000 : ℚ) (1571/640 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1013 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (1571/640 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/2000 : ℚ) (76979/32000 : ℚ) (1571/640 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_1011 node_1012

theorem node_1014 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (1571/640 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_one (4713/2000 : ℚ) (1571/640 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_1010 node_1013

theorem node_1015 : Certificate fc_leaf
    (planeBox (1571/640 : ℚ) (80121/32000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1016 : Certificate fc_leaf
    (planeBox (1571/640 : ℚ) (80121/32000 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1017 : Certificate fc_leaf
    (planeBox (1571/640 : ℚ) (80121/32000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_one (1571/640 : ℚ) (80121/32000 : ℚ) (0 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_1015 node_1016

theorem node_1018 : Certificate fc_leaf
    (planeBox (80121/32000 : ℚ) (161813/64000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1019 : Certificate fc_leaf
    (planeBox (161813/64000 : ℚ) (20423/8000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1020 : Certificate fc_leaf
    (planeBox (80121/32000 : ℚ) (20423/8000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  exact planeBox_split_zero (80121/32000 : ℚ) (161813/64000 : ℚ) (20423/8000 : ℚ) (0 : ℚ) (1571/32000 : ℚ) (by norm_num) (by norm_num)
    node_1018 node_1019

theorem node_1021 : Certificate fc_leaf
    (planeBox (80121/32000 : ℚ) (20423/8000 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1022 : Certificate fc_leaf
    (planeBox (80121/32000 : ℚ) (20423/8000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_one (80121/32000 : ℚ) (20423/8000 : ℚ) (0 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_1020 node_1021

theorem node_1023 : Certificate fc_leaf
    (planeBox (1571/640 : ℚ) (20423/8000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/640 : ℚ) (80121/32000 : ℚ) (20423/8000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_1017 node_1022

theorem node_1024 : Certificate fc_leaf
    (planeBox (1571/640 : ℚ) (80121/32000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1025 : Certificate fc_leaf
    (planeBox (80121/32000 : ℚ) (20423/8000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1026 : Certificate fc_leaf
    (planeBox (1571/640 : ℚ) (20423/8000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/640 : ℚ) (80121/32000 : ℚ) (20423/8000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_1024 node_1025

theorem node_1027 : Certificate fc_leaf
    (planeBox (1571/640 : ℚ) (20423/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_one (1571/640 : ℚ) (20423/8000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_1023 node_1026

theorem node_1028 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (20423/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/2000 : ℚ) (1571/640 : ℚ) (20423/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_1014 node_1027

theorem node_1029 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (1571/640 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1030 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (1571/640 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1031 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (1571/640 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (4713/2000 : ℚ) (1571/640 : ℚ) (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_1029 node_1030

theorem node_1032 : Certificate fc_leaf
    (planeBox (1571/640 : ℚ) (20423/8000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1033 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (20423/8000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (4713/2000 : ℚ) (1571/640 : ℚ) (20423/8000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_1031 node_1032

theorem node_1034 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (20423/8000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (4713/2000 : ℚ) (20423/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_1028 node_1033

theorem node_1035 : Certificate fc_leaf
    (planeBox (20423/8000 : ℚ) (32991/12800 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1036 : Certificate fc_leaf
    (planeBox (32991/12800 : ℚ) (83263/32000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1037 : Certificate fc_leaf
    (planeBox (20423/8000 : ℚ) (83263/32000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  exact planeBox_split_zero (20423/8000 : ℚ) (32991/12800 : ℚ) (83263/32000 : ℚ) (0 : ℚ) (1571/32000 : ℚ) (by norm_num) (by norm_num)
    node_1035 node_1036

theorem node_1038 : Certificate fc_leaf
    (planeBox (20423/8000 : ℚ) (83263/32000 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1039 : Certificate fc_leaf
    (planeBox (20423/8000 : ℚ) (83263/32000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_one (20423/8000 : ℚ) (83263/32000 : ℚ) (0 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_1037 node_1038

theorem node_1040 : Certificate fc_leaf
    (planeBox (83263/32000 : ℚ) (168097/64000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1041 : Certificate fc_leaf
    (planeBox (168097/64000 : ℚ) (42417/16000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1042 : Certificate fc_leaf
    (planeBox (83263/32000 : ℚ) (42417/16000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  exact planeBox_split_zero (83263/32000 : ℚ) (168097/64000 : ℚ) (42417/16000 : ℚ) (0 : ℚ) (1571/32000 : ℚ) (by norm_num) (by norm_num)
    node_1040 node_1041

theorem node_1043 : Certificate fc_leaf
    (planeBox (83263/32000 : ℚ) (42417/16000 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1044 : Certificate fc_leaf
    (planeBox (83263/32000 : ℚ) (42417/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_one (83263/32000 : ℚ) (42417/16000 : ℚ) (0 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_1042 node_1043

theorem node_1045 : Certificate fc_leaf
    (planeBox (20423/8000 : ℚ) (42417/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_zero (20423/8000 : ℚ) (83263/32000 : ℚ) (42417/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_1039 node_1044

theorem node_1046 : Certificate fc_leaf
    (planeBox (20423/8000 : ℚ) (83263/32000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1047 : Certificate fc_leaf
    (planeBox (83263/32000 : ℚ) (42417/16000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1048 : Certificate fc_leaf
    (planeBox (20423/8000 : ℚ) (42417/16000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (20423/8000 : ℚ) (83263/32000 : ℚ) (42417/16000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_1046 node_1047

theorem node_1049 : Certificate fc_leaf
    (planeBox (20423/8000 : ℚ) (42417/16000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_one (20423/8000 : ℚ) (42417/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_1045 node_1048

theorem node_1050 : Certificate fc_leaf
    (planeBox (42417/16000 : ℚ) (171239/64000 : ℚ) (0 : ℚ) (1571/64000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1051 : Certificate fc_leaf
    (planeBox (42417/16000 : ℚ) (171239/64000 : ℚ) (1571/64000 : ℚ) (1571/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1052 : Certificate fc_leaf
    (planeBox (42417/16000 : ℚ) (171239/64000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  exact planeBox_split_one (42417/16000 : ℚ) (171239/64000 : ℚ) (0 : ℚ) (1571/64000 : ℚ) (1571/32000 : ℚ) (by norm_num) (by norm_num)
    node_1050 node_1051

theorem node_1053 : Certificate fc_leaf
    (planeBox (171239/64000 : ℚ) (17281/6400 : ℚ) (0 : ℚ) (1571/64000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1054 : Certificate fc_leaf
    (planeBox (171239/64000 : ℚ) (17281/6400 : ℚ) (1571/64000 : ℚ) (1571/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1055 : Certificate fc_leaf
    (planeBox (171239/64000 : ℚ) (17281/6400 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  exact planeBox_split_one (171239/64000 : ℚ) (17281/6400 : ℚ) (0 : ℚ) (1571/64000 : ℚ) (1571/32000 : ℚ) (by norm_num) (by norm_num)
    node_1053 node_1054

theorem node_1056 : Certificate fc_leaf
    (planeBox (42417/16000 : ℚ) (17281/6400 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  exact planeBox_split_zero (42417/16000 : ℚ) (171239/64000 : ℚ) (17281/6400 : ℚ) (0 : ℚ) (1571/32000 : ℚ) (by norm_num) (by norm_num)
    node_1052 node_1055

theorem node_1057 : Certificate fc_leaf
    (planeBox (42417/16000 : ℚ) (17281/6400 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1058 : Certificate fc_leaf
    (planeBox (42417/16000 : ℚ) (17281/6400 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_one (42417/16000 : ℚ) (17281/6400 : ℚ) (0 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_1056 node_1057

theorem node_1059 : Certificate fc_leaf
    (planeBox (17281/6400 : ℚ) (174381/64000 : ℚ) (0 : ℚ) (1571/64000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1060 : Certificate fc_leaf
    (planeBox (17281/6400 : ℚ) (174381/64000 : ℚ) (1571/64000 : ℚ) (1571/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1061 : Certificate fc_leaf
    (planeBox (17281/6400 : ℚ) (174381/64000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  exact planeBox_split_one (17281/6400 : ℚ) (174381/64000 : ℚ) (0 : ℚ) (1571/64000 : ℚ) (1571/32000 : ℚ) (by norm_num) (by norm_num)
    node_1059 node_1060

theorem node_1062 : Certificate fc_leaf
    (planeBox (174381/64000 : ℚ) (10997/4000 : ℚ) (0 : ℚ) (1571/64000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1063 : Certificate fc_leaf
    (planeBox (174381/64000 : ℚ) (10997/4000 : ℚ) (1571/64000 : ℚ) (1571/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1064 : Certificate fc_leaf
    (planeBox (174381/64000 : ℚ) (10997/4000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  exact planeBox_split_one (174381/64000 : ℚ) (10997/4000 : ℚ) (0 : ℚ) (1571/64000 : ℚ) (1571/32000 : ℚ) (by norm_num) (by norm_num)
    node_1062 node_1063

theorem node_1065 : Certificate fc_leaf
    (planeBox (17281/6400 : ℚ) (10997/4000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  exact planeBox_split_zero (17281/6400 : ℚ) (174381/64000 : ℚ) (10997/4000 : ℚ) (0 : ℚ) (1571/32000 : ℚ) (by norm_num) (by norm_num)
    node_1061 node_1064

theorem node_1066 : Certificate fc_leaf
    (planeBox (17281/6400 : ℚ) (10997/4000 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1067 : Certificate fc_leaf
    (planeBox (17281/6400 : ℚ) (10997/4000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_one (17281/6400 : ℚ) (10997/4000 : ℚ) (0 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_1065 node_1066

theorem node_1068 : Certificate fc_leaf
    (planeBox (42417/16000 : ℚ) (10997/4000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_zero (42417/16000 : ℚ) (17281/6400 : ℚ) (10997/4000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_1058 node_1067

theorem node_1069 : Certificate fc_leaf
    (planeBox (42417/16000 : ℚ) (10997/4000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1070 : Certificate fc_leaf
    (planeBox (42417/16000 : ℚ) (10997/4000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_one (42417/16000 : ℚ) (10997/4000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_1068 node_1069

theorem node_1071 : Certificate fc_leaf
    (planeBox (20423/8000 : ℚ) (10997/4000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (20423/8000 : ℚ) (42417/16000 : ℚ) (10997/4000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_1049 node_1070

theorem node_1072 : Certificate fc_leaf
    (planeBox (20423/8000 : ℚ) (42417/16000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1073 : Certificate fc_leaf
    (planeBox (42417/16000 : ℚ) (10997/4000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1074 : Certificate fc_leaf
    (planeBox (20423/8000 : ℚ) (10997/4000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (20423/8000 : ℚ) (42417/16000 : ℚ) (10997/4000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_1072 node_1073

theorem node_1075 : Certificate fc_leaf
    (planeBox (20423/8000 : ℚ) (10997/4000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (20423/8000 : ℚ) (10997/4000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_1071 node_1074

theorem node_1076 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (10997/4000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (4713/2000 : ℚ) (20423/8000 : ℚ) (10997/4000 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_1034 node_1075

theorem node_1077 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (1571/640 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1078 : Certificate fc_leaf
    (planeBox (1571/640 : ℚ) (20423/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1079 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (20423/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/2000 : ℚ) (1571/640 : ℚ) (20423/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    node_1077 node_1078

theorem node_1080 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (20423/8000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1081 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (20423/8000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (4713/2000 : ℚ) (20423/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_1079 node_1080

theorem node_1082 : Certificate fc_leaf
    (planeBox (20423/8000 : ℚ) (10997/4000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1083 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (10997/4000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (4713/2000 : ℚ) (20423/8000 : ℚ) (10997/4000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_1081 node_1082

theorem node_1084 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (10997/4000 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (4713/2000 : ℚ) (10997/4000 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_1076 node_1083

theorem node_1085 : Certificate fc_leaf
    (planeBox (10997/4000 : ℚ) (177523/64000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1086 : Certificate fc_leaf
    (planeBox (177523/64000 : ℚ) (89547/32000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1087 : Certificate fc_leaf
    (planeBox (10997/4000 : ℚ) (89547/32000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  exact planeBox_split_zero (10997/4000 : ℚ) (177523/64000 : ℚ) (89547/32000 : ℚ) (0 : ℚ) (1571/32000 : ℚ) (by norm_num) (by norm_num)
    node_1085 node_1086

theorem node_1088 : Certificate fc_leaf
    (planeBox (10997/4000 : ℚ) (89547/32000 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1089 : Certificate fc_leaf
    (planeBox (10997/4000 : ℚ) (89547/32000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_one (10997/4000 : ℚ) (89547/32000 : ℚ) (0 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_1087 node_1088

theorem node_1090 : Certificate fc_leaf
    (planeBox (89547/32000 : ℚ) (36133/12800 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1091 : Certificate fc_leaf
    (planeBox (36133/12800 : ℚ) (45559/16000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1092 : Certificate fc_leaf
    (planeBox (89547/32000 : ℚ) (45559/16000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  exact planeBox_split_zero (89547/32000 : ℚ) (36133/12800 : ℚ) (45559/16000 : ℚ) (0 : ℚ) (1571/32000 : ℚ) (by norm_num) (by norm_num)
    node_1090 node_1091

theorem node_1093 : Certificate fc_leaf
    (planeBox (89547/32000 : ℚ) (45559/16000 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1094 : Certificate fc_leaf
    (planeBox (89547/32000 : ℚ) (45559/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_one (89547/32000 : ℚ) (45559/16000 : ℚ) (0 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_1092 node_1093

theorem node_1095 : Certificate fc_leaf
    (planeBox (10997/4000 : ℚ) (45559/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_zero (10997/4000 : ℚ) (89547/32000 : ℚ) (45559/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_1089 node_1094

theorem node_1096 : Certificate fc_leaf
    (planeBox (10997/4000 : ℚ) (45559/16000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1097 : Certificate fc_leaf
    (planeBox (10997/4000 : ℚ) (45559/16000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_one (10997/4000 : ℚ) (45559/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_1095 node_1096

theorem node_1098 : Certificate fc_leaf
    (planeBox (45559/16000 : ℚ) (183807/64000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1099 : Certificate fc_leaf
    (planeBox (183807/64000 : ℚ) (92689/32000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1100 : Certificate fc_leaf
    (planeBox (45559/16000 : ℚ) (92689/32000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  exact planeBox_split_zero (45559/16000 : ℚ) (183807/64000 : ℚ) (92689/32000 : ℚ) (0 : ℚ) (1571/32000 : ℚ) (by norm_num) (by norm_num)
    node_1098 node_1099

theorem node_1101 : Certificate fc_leaf
    (planeBox (45559/16000 : ℚ) (92689/32000 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1102 : Certificate fc_leaf
    (planeBox (45559/16000 : ℚ) (92689/32000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_one (45559/16000 : ℚ) (92689/32000 : ℚ) (0 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_1100 node_1101

theorem node_1103 : Certificate fc_leaf
    (planeBox (92689/32000 : ℚ) (186949/64000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1104 : Certificate fc_leaf
    (planeBox (186949/64000 : ℚ) (4713/1600 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1105 : Certificate fc_leaf
    (planeBox (92689/32000 : ℚ) (4713/1600 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  exact planeBox_split_zero (92689/32000 : ℚ) (186949/64000 : ℚ) (4713/1600 : ℚ) (0 : ℚ) (1571/32000 : ℚ) (by norm_num) (by norm_num)
    node_1103 node_1104

theorem node_1106 : Certificate fc_leaf
    (planeBox (92689/32000 : ℚ) (4713/1600 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1107 : Certificate fc_leaf
    (planeBox (92689/32000 : ℚ) (4713/1600 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_one (92689/32000 : ℚ) (4713/1600 : ℚ) (0 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_1105 node_1106

theorem node_1108 : Certificate fc_leaf
    (planeBox (45559/16000 : ℚ) (4713/1600 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_zero (45559/16000 : ℚ) (92689/32000 : ℚ) (4713/1600 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_1102 node_1107

theorem node_1109 : Certificate fc_leaf
    (planeBox (45559/16000 : ℚ) (4713/1600 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1110 : Certificate fc_leaf
    (planeBox (45559/16000 : ℚ) (4713/1600 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_one (45559/16000 : ℚ) (4713/1600 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_1108 node_1109

theorem node_1111 : Certificate fc_leaf
    (planeBox (10997/4000 : ℚ) (4713/1600 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (10997/4000 : ℚ) (45559/16000 : ℚ) (4713/1600 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_1097 node_1110

theorem node_1112 : Certificate fc_leaf
    (planeBox (10997/4000 : ℚ) (4713/1600 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1113 : Certificate fc_leaf
    (planeBox (10997/4000 : ℚ) (4713/1600 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (10997/4000 : ℚ) (4713/1600 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_1111 node_1112

theorem node_1114 : Certificate fc_leaf
    (planeBox (4713/1600 : ℚ) (95831/32000 : ℚ) (0 : ℚ) (1571/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1115 : Certificate fc_leaf
    (planeBox (4713/1600 : ℚ) (95831/32000 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1116 : Certificate fc_leaf
    (planeBox (4713/1600 : ℚ) (95831/32000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_one (4713/1600 : ℚ) (95831/32000 : ℚ) (0 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_1114 node_1115

theorem node_1117 : Certificate fc_leaf
    (planeBox (95831/32000 : ℚ) (48701/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1118 : Certificate fc_leaf
    (planeBox (4713/1600 : ℚ) (48701/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ)) := by
  exact planeBox_split_zero (4713/1600 : ℚ) (95831/32000 : ℚ) (48701/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (by norm_num) (by norm_num)
    node_1116 node_1117

theorem node_1119 : Certificate fc_leaf
    (planeBox (4713/1600 : ℚ) (48701/16000 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1120 : Certificate fc_leaf
    (planeBox (4713/1600 : ℚ) (48701/16000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_one (4713/1600 : ℚ) (48701/16000 : ℚ) (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_1118 node_1119

theorem node_1121 : Certificate fc_leaf
    (planeBox (48701/16000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1122 : Certificate fc_leaf
    (planeBox (4713/1600 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/1600 : ℚ) (48701/16000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    node_1120 node_1121

theorem node_1123 : Certificate fc_leaf
    (planeBox (4713/1600 : ℚ) (1571/500 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_1124 : Certificate fc_leaf
    (planeBox (4713/1600 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (4713/1600 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_1122 node_1123

theorem node_1125 : Certificate fc_leaf
    (planeBox (10997/4000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (10997/4000 : ℚ) (4713/1600 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    node_1113 node_1124

theorem node_1126 : Certificate fc_leaf
    (planeBox (10997/4000 : ℚ) (1571/500 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_1127 : Certificate fc_leaf
    (planeBox (10997/4000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (10997/4000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_1125 node_1126

theorem node_1128 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (4713/2000 : ℚ) (10997/4000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_1084 node_1127

theorem node_1129 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (1571/500 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_1130 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (4713/2000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_1128 node_1129

theorem node_1131 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (1571/1000 : ℚ) (4713/2000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_1003 node_1130

theorem node_1132 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (1571/500 : ℚ) (1571/1000 : ℚ) (1571/500 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_1133 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/500 : ℚ)) := by
  exact planeBox_split_one (1571/1000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/1000 : ℚ) (1571/500 : ℚ) (by norm_num) (by norm_num)
    node_1131 node_1132

theorem node_1134 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/500 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/1000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/500 : ℚ) (by norm_num) (by norm_num)
    node_882 node_1133

/-- `EfficientFaceCertificate` for this face (FaceCertificate.plane, root as in A25 Face1). -/
def certificate : SharedMomentEfficientFactorCertificate.EfficientFaceCertificate fc_p fc_q fc_b fc_bound :=
  .base (.plane (planeBox (0 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/500 : ℚ))
    (by intro i; fin_cases i <;> norm_num [planeBox,RatInterval.piHi]) node_1134)
end N11Formalization.Class33FaceTreeQ0M2F1_2_9
#print axioms N11Formalization.Class33FaceTreeQ0M2F1_2_9.node_1134
