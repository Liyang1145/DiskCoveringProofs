import N11Formalization.SharedMomentConcreteFace1Data
import N11Formalization.SharedMomentEfficientFactorCertificate

/-! Class33 DRAFT (uncompiled): q0m2 face {0,9,10} canonical coefficients, plane tree,
362 leaves (exact Python pre-validation of every leaf, py/face_kernel.py). -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.Class33FaceTreeQ0M2F0_9_10
open RationalBoxSubdivision SharedMomentFacePlaneGradientCertificate SharedMomentFacePlaneCertificate
open SharedMomentFacePlaneDirectCertificate SharedMomentFactorRationalNodes
open SharedMomentFactorIntervalCertificate SharedMomentFactorLocalGradientCertificate
open RationalTrigLocalLipschitz SharedMomentConcreteFace1

def fc_p : Fin 3 → ℚ := ![(-40768173/500000000 : ℚ),(10358433/500000000 : ℚ),(-40776373/125000000 : ℚ)]
def fc_q : Fin 3 → ℚ := ![(2362171/1000000000 : ℚ),(-302170431/1000000000 : ℚ),(68861399/1000000000 : ℚ)]
def fc_b : Fin 3 → ℚ := ![(-2930609/1000000000 : ℚ),(510491171/1000000000 : ℚ),(2033293/15625000 : ℚ)]
def fc_bound : ℚ := (201189/1000000 : ℚ)
def fc_leaf (B : Cell (Fin 2)) : Prop :=
  GradientPlaneLeaf fc_p fc_q fc_b fc_bound B

theorem node_0 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_1 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_2 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_3 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_1 node_2

theorem node_4 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_0 node_3

theorem node_5 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_6 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_7 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_8 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_9 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (1571/4000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_7 node_8

theorem node_10 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_6 node_9

theorem node_11 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_5 node_10

theorem node_12 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_13 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_14 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_12 node_13

theorem node_15 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_16 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_17 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_15 node_16

theorem node_18 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_14 node_17

theorem node_19 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_20 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_21 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_22 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_20 node_21

theorem node_23 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (4713/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_19 node_22

theorem node_24 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_25 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_26 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_27 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_25 node_26

theorem node_28 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_24 node_27

theorem node_29 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_30 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_31 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (10997/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_29 node_30

theorem node_32 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_33 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_34 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_35 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_33 node_34

theorem node_36 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (1571/2000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_32 node_35

theorem node_37 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_31 node_36

theorem node_38 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_28 node_37

theorem node_39 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_23 node_38

theorem node_40 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_18 node_39

theorem node_41 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_11 node_40

theorem node_42 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_4 node_41

theorem node_43 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (4713/4000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_44 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_45 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_46 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_47 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_45 node_46

theorem node_48 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_44 node_47

theorem node_49 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (4713/4000 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (4713/4000 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_43 node_48

theorem node_50 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_51 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_52 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_53 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_51 node_52

theorem node_54 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_55 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_56 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_54 node_55

theorem node_57 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_53 node_56

theorem node_58 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_50 node_57

theorem node_59 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_49 node_58

theorem node_60 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_61 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_62 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_63 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_64 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_62 node_63

theorem node_65 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_61 node_64

theorem node_66 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_60 node_65

theorem node_67 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_68 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_69 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_67 node_68

theorem node_70 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_71 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_72 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_70 node_71

theorem node_73 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_74 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_75 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_73 node_74

theorem node_76 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_72 node_75

theorem node_77 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_69 node_76

theorem node_78 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_66 node_77

theorem node_79 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_80 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_81 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_82 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_80 node_81

theorem node_83 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (14139/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_79 node_82

theorem node_84 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_85 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_86 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (by norm_num) (by norm_num)
    node_84 node_85

theorem node_87 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (20423/16000 : ℚ) (42417/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_88 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (42417/32000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_89 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (29849/32000 : ℚ) (20423/16000 : ℚ) (42417/32000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_87 node_88

theorem node_90 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (20423/16000 : ℚ) (42417/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_91 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (42417/32000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_92 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (29849/32000 : ℚ) (1571/1600 : ℚ) (20423/16000 : ℚ) (42417/32000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_90 node_91

theorem node_93 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_89 node_92

theorem node_94 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_86 node_93

theorem node_95 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_83 node_94

theorem node_96 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_97 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (10997/8000 : ℚ) (45559/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_98 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (45559/32000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_99 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  exact planeBox_split_one (26707/32000 : ℚ) (14139/16000 : ℚ) (10997/8000 : ℚ) (45559/32000 : ℚ) (4713/3200 : ℚ) (by norm_num) (by norm_num)
    node_97 node_98

theorem node_100 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (by norm_num) (by norm_num)
    node_96 node_99

theorem node_101 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (4713/3200 : ℚ) (48701/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_102 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (48701/32000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_103 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (26707/32000 : ℚ) (4713/3200 : ℚ) (48701/32000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_101 node_102

theorem node_104 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (4713/3200 : ℚ) (48701/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_105 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (48701/32000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_106 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (26707/32000 : ℚ) (14139/16000 : ℚ) (4713/3200 : ℚ) (48701/32000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_104 node_105

theorem node_107 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_103 node_106

theorem node_108 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (14139/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_100 node_107

theorem node_109 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (10997/8000 : ℚ) (45559/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_110 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (45559/32000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_111 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (29849/32000 : ℚ) (10997/8000 : ℚ) (45559/32000 : ℚ) (4713/3200 : ℚ) (by norm_num) (by norm_num)
    node_109 node_110

theorem node_112 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (10997/8000 : ℚ) (45559/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_113 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (45559/32000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_114 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  exact planeBox_split_one (29849/32000 : ℚ) (1571/1600 : ℚ) (10997/8000 : ℚ) (45559/32000 : ℚ) (4713/3200 : ℚ) (by norm_num) (by norm_num)
    node_112 node_113

theorem node_115 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (by norm_num) (by norm_num)
    node_111 node_114

theorem node_116 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (4713/3200 : ℚ) (48701/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_117 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (48701/32000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_118 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (29849/32000 : ℚ) (4713/3200 : ℚ) (48701/32000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_116 node_117

theorem node_119 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (4713/3200 : ℚ) (48701/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_120 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (48701/32000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_121 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (29849/32000 : ℚ) (1571/1600 : ℚ) (4713/3200 : ℚ) (48701/32000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_119 node_120

theorem node_122 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_118 node_121

theorem node_123 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (1571/1600 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_115 node_122

theorem node_124 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_108 node_123

theorem node_125 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_95 node_124

theorem node_126 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_127 : Certificate fc_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/1280 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_128 : Certificate fc_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (1571/1280 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_129 : Certificate fc_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  exact planeBox_split_one (32991/32000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/1280 : ℚ) (20423/16000 : ℚ) (by norm_num) (by norm_num)
    node_127 node_128

theorem node_130 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (by norm_num) (by norm_num)
    node_126 node_129

theorem node_131 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (20423/16000 : ℚ) (42417/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_132 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (42417/32000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_133 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (32991/32000 : ℚ) (20423/16000 : ℚ) (42417/32000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_131 node_132

theorem node_134 : Certificate fc_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (20423/16000 : ℚ) (42417/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_135 : Certificate fc_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (42417/32000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_136 : Certificate fc_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (32991/32000 : ℚ) (17281/16000 : ℚ) (20423/16000 : ℚ) (42417/32000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_134 node_135

theorem node_137 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_133 node_136

theorem node_138 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_130 node_137

theorem node_139 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_140 : Certificate fc_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_141 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (by norm_num) (by norm_num)
    node_139 node_140

theorem node_142 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (20423/16000 : ℚ) (42417/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_143 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (42417/32000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_144 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (36133/32000 : ℚ) (20423/16000 : ℚ) (42417/32000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_142 node_143

theorem node_145 : Certificate fc_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_146 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_144 node_145

theorem node_147 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_141 node_146

theorem node_148 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_138 node_147

theorem node_149 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (10997/8000 : ℚ) (45559/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_150 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (45559/32000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_151 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (32991/32000 : ℚ) (10997/8000 : ℚ) (45559/32000 : ℚ) (4713/3200 : ℚ) (by norm_num) (by norm_num)
    node_149 node_150

theorem node_152 : Certificate fc_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (10997/8000 : ℚ) (45559/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_153 : Certificate fc_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (45559/32000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_154 : Certificate fc_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  exact planeBox_split_one (32991/32000 : ℚ) (17281/16000 : ℚ) (10997/8000 : ℚ) (45559/32000 : ℚ) (4713/3200 : ℚ) (by norm_num) (by norm_num)
    node_152 node_153

theorem node_155 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (by norm_num) (by norm_num)
    node_151 node_154

theorem node_156 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (4713/3200 : ℚ) (48701/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_157 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (48701/32000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_158 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (32991/32000 : ℚ) (4713/3200 : ℚ) (48701/32000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_156 node_157

theorem node_159 : Certificate fc_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (4713/3200 : ℚ) (48701/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_160 : Certificate fc_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (48701/32000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_161 : Certificate fc_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (32991/32000 : ℚ) (17281/16000 : ℚ) (4713/3200 : ℚ) (48701/32000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_159 node_160

theorem node_162 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_158 node_161

theorem node_163 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (17281/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_155 node_162

theorem node_164 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (10997/8000 : ℚ) (45559/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_165 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (45559/32000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_166 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (36133/32000 : ℚ) (10997/8000 : ℚ) (45559/32000 : ℚ) (4713/3200 : ℚ) (by norm_num) (by norm_num)
    node_164 node_165

theorem node_167 : Certificate fc_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_168 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (by norm_num) (by norm_num)
    node_166 node_167

theorem node_169 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_170 : Certificate fc_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_171 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_169 node_170

theorem node_172 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_168 node_171

theorem node_173 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_163 node_172

theorem node_174 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_148 node_173

theorem node_175 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_125 node_174

theorem node_176 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_78 node_175

theorem node_177 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_178 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_179 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (20423/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_177 node_178

theorem node_180 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_181 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_179 node_180

theorem node_182 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_183 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_184 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (20423/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_182 node_183

theorem node_185 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_186 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_187 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_185 node_186

theorem node_188 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_184 node_187

theorem node_189 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_181 node_188

theorem node_190 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_191 : Certificate fc_leaf
    (planeBox (4713/3200 : ℚ) (1571/1000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_192 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    node_190 node_191

theorem node_193 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_194 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_195 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_193 node_194

theorem node_196 : Certificate fc_leaf
    (planeBox (4713/3200 : ℚ) (1571/1000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_197 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_195 node_196

theorem node_198 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_192 node_197

theorem node_199 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_189 node_198

theorem node_200 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (1571/1280 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_201 : Certificate fc_leaf
    (planeBox (1571/1280 : ℚ) (20423/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_202 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (1571/1280 : ℚ) (20423/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (by norm_num) (by norm_num)
    node_200 node_201

theorem node_203 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (1571/1280 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_204 : Certificate fc_leaf
    (planeBox (1571/1280 : ℚ) (20423/16000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_205 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (1571/1280 : ℚ) (20423/16000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_203 node_204

theorem node_206 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (20423/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_202 node_205

theorem node_207 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_208 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_209 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (20423/16000 : ℚ) (10997/8000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_207 node_208

theorem node_210 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_206 node_209

theorem node_211 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (1571/1280 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_212 : Certificate fc_leaf
    (planeBox (1571/1280 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_213 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (1571/1280 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (by norm_num) (by norm_num)
    node_211 node_212

theorem node_214 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_215 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_213 node_214

theorem node_216 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_217 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_215 node_216

theorem node_218 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (10997/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_210 node_217

theorem node_219 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_220 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_221 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (10997/8000 : ℚ) (4713/3200 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_219 node_220

theorem node_222 : Certificate fc_leaf
    (planeBox (4713/3200 : ℚ) (1571/1000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_223 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    node_221 node_222

theorem node_224 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_225 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (10997/8000 : ℚ) (1571/1000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_223 node_224

theorem node_226 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (1571/1000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_218 node_225

theorem node_227 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_199 node_226

theorem node_228 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_176 node_227

theorem node_229 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_59 node_228

theorem node_230 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_42 node_229

theorem node_231 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_232 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_233 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/8000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_231 node_232

theorem node_234 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_235 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_236 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_237 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_235 node_236

theorem node_238 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_234 node_237

theorem node_239 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_233 node_238

theorem node_240 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_241 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/16000 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_242 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (1571/8000 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_243 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_241 node_242

theorem node_244 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/8000 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_240 node_243

theorem node_245 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_246 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_247 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_248 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ)) := by
  exact planeBox_split_one (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ) (by norm_num) (by norm_num)
    node_246 node_247

theorem node_249 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ) (by norm_num) (by norm_num)
    node_245 node_248

theorem node_250 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_251 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_252 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (4713/16000 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_250 node_251

theorem node_253 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_254 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_255 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (4713/16000 : ℚ) (1571/4000 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_253 node_254

theorem node_256 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_252 node_255

theorem node_257 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_249 node_256

theorem node_258 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_244 node_257

theorem node_259 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (1571/1000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/4000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_239 node_258

theorem node_260 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_261 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_262 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_263 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  exact planeBox_split_one (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ) (by norm_num) (by norm_num)
    node_261 node_262

theorem node_264 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ) (by norm_num) (by norm_num)
    node_260 node_263

theorem node_265 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_266 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_267 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (1571/3200 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_265 node_266

theorem node_268 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_269 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_270 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_271 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_zero (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_269 node_270

theorem node_272 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (1571/3200 : ℚ) (4713/8000 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_268 node_271

theorem node_273 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_267 node_272

theorem node_274 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_264 node_273

theorem node_275 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_276 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_277 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_278 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ) (by norm_num) (by norm_num)
    node_276 node_277

theorem node_279 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ) (by norm_num) (by norm_num)
    node_275 node_278

theorem node_280 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_281 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (51843/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_282 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (51843/32000 : ℚ) (26707/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_283 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ)) := by
  exact planeBox_split_one (4713/6400 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (51843/32000 : ℚ) (26707/16000 : ℚ) (by norm_num) (by norm_num)
    node_281 node_282

theorem node_284 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ) (by norm_num) (by norm_num)
    node_280 node_283

theorem node_285 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_286 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (26707/16000 : ℚ) (10997/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_287 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (10997/6400 : ℚ) (14139/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_288 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ)) := by
  exact planeBox_split_one (4713/6400 : ℚ) (1571/2000 : ℚ) (26707/16000 : ℚ) (10997/6400 : ℚ) (14139/8000 : ℚ) (by norm_num) (by norm_num)
    node_286 node_287

theorem node_289 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ) (by norm_num) (by norm_num)
    node_285 node_288

theorem node_290 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ) (by norm_num) (by norm_num)
    node_284 node_289

theorem node_291 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ) (by norm_num) (by norm_num)
    node_279 node_290

theorem node_292 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_293 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_294 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ) (by norm_num) (by norm_num)
    node_292 node_293

theorem node_295 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_296 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (29849/16000 : ℚ) (61269/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_297 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (61269/32000 : ℚ) (1571/800 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_298 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (20423/32000 : ℚ) (10997/16000 : ℚ) (29849/16000 : ℚ) (61269/32000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_296 node_297

theorem node_299 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_295 node_298

theorem node_300 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (10997/16000 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_294 node_299

theorem node_301 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (14139/8000 : ℚ) (58127/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_302 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (58127/32000 : ℚ) (29849/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_303 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (4713/6400 : ℚ) (14139/8000 : ℚ) (58127/32000 : ℚ) (29849/16000 : ℚ) (by norm_num) (by norm_num)
    node_301 node_302

theorem node_304 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (14139/8000 : ℚ) (58127/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_305 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (58127/32000 : ℚ) (29849/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_306 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ)) := by
  exact planeBox_split_one (4713/6400 : ℚ) (1571/2000 : ℚ) (14139/8000 : ℚ) (58127/32000 : ℚ) (29849/16000 : ℚ) (by norm_num) (by norm_num)
    node_304 node_305

theorem node_307 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ) (by norm_num) (by norm_num)
    node_303 node_306

theorem node_308 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (29849/16000 : ℚ) (61269/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_309 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (61269/32000 : ℚ) (1571/800 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_310 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (4713/6400 : ℚ) (29849/16000 : ℚ) (61269/32000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_308 node_309

theorem node_311 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (29849/16000 : ℚ) (61269/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_312 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (61269/32000 : ℚ) (1571/800 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_313 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (4713/6400 : ℚ) (1571/2000 : ℚ) (29849/16000 : ℚ) (61269/32000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_311 node_312

theorem node_314 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_310 node_313

theorem node_315 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (1571/2000 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_307 node_314

theorem node_316 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_300 node_315

theorem node_317 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_291 node_316

theorem node_318 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_274 node_317

theorem node_319 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_320 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_321 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_322 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ) (by norm_num) (by norm_num)
    node_320 node_321

theorem node_323 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (1571/3200 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ) (by norm_num) (by norm_num)
    node_319 node_322

theorem node_324 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_325 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_326 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ) (by norm_num) (by norm_num)
    node_324 node_325

theorem node_327 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_328 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (32991/16000 : ℚ) (67553/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_329 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (67553/32000 : ℚ) (17281/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_330 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ)) := by
  exact planeBox_split_one (17281/32000 : ℚ) (4713/8000 : ℚ) (32991/16000 : ℚ) (67553/32000 : ℚ) (17281/8000 : ℚ) (by norm_num) (by norm_num)
    node_328 node_329

theorem node_331 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ) (by norm_num) (by norm_num)
    node_327 node_330

theorem node_332 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ)) := by
  exact planeBox_split_one (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ) (by norm_num) (by norm_num)
    node_326 node_331

theorem node_333 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ) (by norm_num) (by norm_num)
    node_323 node_332

theorem node_334 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_335 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_336 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ) (by norm_num) (by norm_num)
    node_334 node_335

theorem node_337 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_338 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_339 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_337 node_338

theorem node_340 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (1571/3200 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_336 node_339

theorem node_341 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (17281/8000 : ℚ) (14139/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_342 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (14139/6400 : ℚ) (36133/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_343 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ)) := by
  exact planeBox_split_one (1571/3200 : ℚ) (17281/32000 : ℚ) (17281/8000 : ℚ) (14139/6400 : ℚ) (36133/16000 : ℚ) (by norm_num) (by norm_num)
    node_341 node_342

theorem node_344 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (17281/8000 : ℚ) (14139/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_345 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (14139/6400 : ℚ) (36133/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_346 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ)) := by
  exact planeBox_split_one (17281/32000 : ℚ) (4713/8000 : ℚ) (17281/8000 : ℚ) (14139/6400 : ℚ) (36133/16000 : ℚ) (by norm_num) (by norm_num)
    node_344 node_345

theorem node_347 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ) (by norm_num) (by norm_num)
    node_343 node_346

theorem node_348 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (36133/16000 : ℚ) (73837/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_349 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (73837/32000 : ℚ) (4713/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_350 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (1571/3200 : ℚ) (17281/32000 : ℚ) (36133/16000 : ℚ) (73837/32000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_348 node_349

theorem node_351 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (36133/16000 : ℚ) (73837/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_352 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (73837/32000 : ℚ) (4713/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_353 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (17281/32000 : ℚ) (4713/8000 : ℚ) (36133/16000 : ℚ) (73837/32000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_351 node_352

theorem node_354 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_350 node_353

theorem node_355 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (1571/3200 : ℚ) (4713/8000 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_347 node_354

theorem node_356 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_340 node_355

theorem node_357 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_333 node_356

theorem node_358 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (1571/800 : ℚ) (64411/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_359 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (64411/32000 : ℚ) (32991/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_360 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (20423/32000 : ℚ) (1571/800 : ℚ) (64411/32000 : ℚ) (32991/16000 : ℚ) (by norm_num) (by norm_num)
    node_358 node_359

theorem node_361 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (1571/800 : ℚ) (64411/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_362 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (64411/32000 : ℚ) (32991/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_363 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ)) := by
  exact planeBox_split_one (20423/32000 : ℚ) (10997/16000 : ℚ) (1571/800 : ℚ) (64411/32000 : ℚ) (32991/16000 : ℚ) (by norm_num) (by norm_num)
    node_361 node_362

theorem node_364 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ) (by norm_num) (by norm_num)
    node_360 node_363

theorem node_365 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (32991/16000 : ℚ) (67553/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_366 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (67553/32000 : ℚ) (17281/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_367 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (20423/32000 : ℚ) (32991/16000 : ℚ) (67553/32000 : ℚ) (17281/8000 : ℚ) (by norm_num) (by norm_num)
    node_365 node_366

theorem node_368 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (32991/16000 : ℚ) (67553/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_369 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (67553/32000 : ℚ) (17281/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_370 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ)) := by
  exact planeBox_split_one (20423/32000 : ℚ) (10997/16000 : ℚ) (32991/16000 : ℚ) (67553/32000 : ℚ) (17281/8000 : ℚ) (by norm_num) (by norm_num)
    node_368 node_369

theorem node_371 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ) (by norm_num) (by norm_num)
    node_367 node_370

theorem node_372 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ) (by norm_num) (by norm_num)
    node_364 node_371

theorem node_373 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/800 : ℚ) (64411/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_374 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (64411/32000 : ℚ) (32991/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_375 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/800 : ℚ) (64411/32000 : ℚ) (32991/16000 : ℚ) (by norm_num) (by norm_num)
    node_373 node_374

theorem node_376 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (1571/800 : ℚ) (64411/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_377 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (64411/32000 : ℚ) (32991/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_378 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ)) := by
  exact planeBox_split_one (4713/6400 : ℚ) (1571/2000 : ℚ) (1571/800 : ℚ) (64411/32000 : ℚ) (32991/16000 : ℚ) (by norm_num) (by norm_num)
    node_376 node_377

theorem node_379 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ) (by norm_num) (by norm_num)
    node_375 node_378

theorem node_380 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (32991/16000 : ℚ) (67553/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_381 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (67553/32000 : ℚ) (17281/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_382 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (4713/6400 : ℚ) (32991/16000 : ℚ) (67553/32000 : ℚ) (17281/8000 : ℚ) (by norm_num) (by norm_num)
    node_380 node_381

theorem node_383 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (32991/16000 : ℚ) (67553/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_384 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (67553/32000 : ℚ) (17281/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_385 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ)) := by
  exact planeBox_split_one (4713/6400 : ℚ) (1571/2000 : ℚ) (32991/16000 : ℚ) (67553/32000 : ℚ) (17281/8000 : ℚ) (by norm_num) (by norm_num)
    node_383 node_384

theorem node_386 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ) (by norm_num) (by norm_num)
    node_382 node_385

theorem node_387 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ) (by norm_num) (by norm_num)
    node_379 node_386

theorem node_388 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ) (by norm_num) (by norm_num)
    node_372 node_387

theorem node_389 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (17281/8000 : ℚ) (14139/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_390 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (14139/6400 : ℚ) (36133/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_391 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (20423/32000 : ℚ) (17281/8000 : ℚ) (14139/6400 : ℚ) (36133/16000 : ℚ) (by norm_num) (by norm_num)
    node_389 node_390

theorem node_392 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (17281/8000 : ℚ) (14139/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_393 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (14139/6400 : ℚ) (36133/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_394 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ)) := by
  exact planeBox_split_one (20423/32000 : ℚ) (10997/16000 : ℚ) (17281/8000 : ℚ) (14139/6400 : ℚ) (36133/16000 : ℚ) (by norm_num) (by norm_num)
    node_392 node_393

theorem node_395 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ) (by norm_num) (by norm_num)
    node_391 node_394

theorem node_396 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (36133/16000 : ℚ) (73837/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_397 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (73837/32000 : ℚ) (4713/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_398 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (20423/32000 : ℚ) (36133/16000 : ℚ) (73837/32000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_396 node_397

theorem node_399 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (36133/16000 : ℚ) (73837/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_400 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (73837/32000 : ℚ) (4713/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_401 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (20423/32000 : ℚ) (10997/16000 : ℚ) (36133/16000 : ℚ) (73837/32000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_399 node_400

theorem node_402 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_398 node_401

theorem node_403 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (10997/16000 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_395 node_402

theorem node_404 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (17281/8000 : ℚ) (14139/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_405 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (14139/6400 : ℚ) (36133/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_406 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (4713/6400 : ℚ) (17281/8000 : ℚ) (14139/6400 : ℚ) (36133/16000 : ℚ) (by norm_num) (by norm_num)
    node_404 node_405

theorem node_407 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (17281/8000 : ℚ) (14139/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_408 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (14139/6400 : ℚ) (36133/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_409 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ)) := by
  exact planeBox_split_one (4713/6400 : ℚ) (1571/2000 : ℚ) (17281/8000 : ℚ) (14139/6400 : ℚ) (36133/16000 : ℚ) (by norm_num) (by norm_num)
    node_407 node_408

theorem node_410 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ) (by norm_num) (by norm_num)
    node_406 node_409

theorem node_411 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (36133/16000 : ℚ) (73837/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_412 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (73837/32000 : ℚ) (4713/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_413 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (4713/6400 : ℚ) (36133/16000 : ℚ) (73837/32000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_411 node_412

theorem node_414 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (36133/16000 : ℚ) (73837/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_415 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (73837/32000 : ℚ) (4713/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_416 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (4713/6400 : ℚ) (1571/2000 : ℚ) (36133/16000 : ℚ) (73837/32000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_414 node_415

theorem node_417 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_413 node_416

theorem node_418 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (1571/2000 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_410 node_417

theorem node_419 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_403 node_418

theorem node_420 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_388 node_419

theorem node_421 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_357 node_420

theorem node_422 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_318 node_421

theorem node_423 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_259 node_422

theorem node_424 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/16000 : ℚ) (4713/2000 : ℚ) (20423/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_425 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (1571/8000 : ℚ) (4713/2000 : ℚ) (20423/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_426 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (4713/2000 : ℚ) (20423/8000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (4713/2000 : ℚ) (20423/8000 : ℚ) (by norm_num) (by norm_num)
    node_424 node_425

theorem node_427 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/16000 : ℚ) (20423/8000 : ℚ) (10997/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_428 : Certificate fc_leaf
    (planeBox (1571/16000 : ℚ) (1571/8000 : ℚ) (20423/8000 : ℚ) (10997/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_429 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (20423/8000 : ℚ) (10997/4000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (20423/8000 : ℚ) (10997/4000 : ℚ) (by norm_num) (by norm_num)
    node_427 node_428

theorem node_430 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (4713/2000 : ℚ) (10997/4000 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/8000 : ℚ) (4713/2000 : ℚ) (20423/8000 : ℚ) (10997/4000 : ℚ) (by norm_num) (by norm_num)
    node_426 node_429

theorem node_431 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (4713/2000 : ℚ) (1571/640 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_432 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/640 : ℚ) (20423/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_433 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (4713/2000 : ℚ) (20423/8000 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (4713/16000 : ℚ) (4713/2000 : ℚ) (1571/640 : ℚ) (20423/8000 : ℚ) (by norm_num) (by norm_num)
    node_431 node_432

theorem node_434 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (4713/2000 : ℚ) (1571/640 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_435 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/640 : ℚ) (20423/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_436 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (4713/2000 : ℚ) (20423/8000 : ℚ)) := by
  exact planeBox_split_one (4713/16000 : ℚ) (1571/4000 : ℚ) (4713/2000 : ℚ) (1571/640 : ℚ) (20423/8000 : ℚ) (by norm_num) (by norm_num)
    node_434 node_435

theorem node_437 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (4713/2000 : ℚ) (20423/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (4713/2000 : ℚ) (20423/8000 : ℚ) (by norm_num) (by norm_num)
    node_433 node_436

theorem node_438 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (20423/8000 : ℚ) (42417/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_439 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (42417/16000 : ℚ) (10997/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_440 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (20423/8000 : ℚ) (10997/4000 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (4713/16000 : ℚ) (20423/8000 : ℚ) (42417/16000 : ℚ) (10997/4000 : ℚ) (by norm_num) (by norm_num)
    node_438 node_439

theorem node_441 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (20423/8000 : ℚ) (42417/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_442 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (42417/16000 : ℚ) (10997/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_443 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (20423/8000 : ℚ) (10997/4000 : ℚ)) := by
  exact planeBox_split_one (4713/16000 : ℚ) (1571/4000 : ℚ) (20423/8000 : ℚ) (42417/16000 : ℚ) (10997/4000 : ℚ) (by norm_num) (by norm_num)
    node_441 node_442

theorem node_444 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (20423/8000 : ℚ) (10997/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (20423/8000 : ℚ) (10997/4000 : ℚ) (by norm_num) (by norm_num)
    node_440 node_443

theorem node_445 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (4713/2000 : ℚ) (10997/4000 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (1571/4000 : ℚ) (4713/2000 : ℚ) (20423/8000 : ℚ) (10997/4000 : ℚ) (by norm_num) (by norm_num)
    node_437 node_444

theorem node_446 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (4713/2000 : ℚ) (10997/4000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (4713/2000 : ℚ) (10997/4000 : ℚ) (by norm_num) (by norm_num)
    node_430 node_445

theorem node_447 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (10997/4000 : ℚ) (4713/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_448 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (4713/1600 : ℚ) (1571/500 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_449 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (10997/4000 : ℚ) (1571/500 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/8000 : ℚ) (10997/4000 : ℚ) (4713/1600 : ℚ) (1571/500 : ℚ) (by norm_num) (by norm_num)
    node_447 node_448

theorem node_450 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (10997/4000 : ℚ) (4713/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_451 : Certificate fc_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (10997/4000 : ℚ) (4713/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_452 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (10997/4000 : ℚ) (4713/1600 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (10997/4000 : ℚ) (4713/1600 : ℚ) (by norm_num) (by norm_num)
    node_450 node_451

theorem node_453 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (4713/1600 : ℚ) (1571/500 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_454 : Certificate fc_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (10997/4000 : ℚ) (1571/500 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (1571/4000 : ℚ) (10997/4000 : ℚ) (4713/1600 : ℚ) (1571/500 : ℚ) (by norm_num) (by norm_num)
    node_452 node_453

theorem node_455 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (10997/4000 : ℚ) (1571/500 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (10997/4000 : ℚ) (1571/500 : ℚ) (by norm_num) (by norm_num)
    node_449 node_454

theorem node_456 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (4713/2000 : ℚ) (1571/500 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/4000 : ℚ) (4713/2000 : ℚ) (10997/4000 : ℚ) (1571/500 : ℚ) (by norm_num) (by norm_num)
    node_446 node_455

theorem node_457 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (4713/2000 : ℚ) (1571/640 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_458 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (4713/2000 : ℚ) (1571/640 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_459 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/2000 : ℚ) (1571/640 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (4713/2000 : ℚ) (1571/640 : ℚ) (by norm_num) (by norm_num)
    node_457 node_458

theorem node_460 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/640 : ℚ) (20423/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_461 : Certificate fc_leaf
    (planeBox (14139/32000 : ℚ) (1571/3200 : ℚ) (1571/640 : ℚ) (20423/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_462 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (1571/640 : ℚ) (20423/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ) (1571/640 : ℚ) (20423/8000 : ℚ) (by norm_num) (by norm_num)
    node_460 node_461

theorem node_463 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/2000 : ℚ) (20423/8000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/2000 : ℚ) (1571/640 : ℚ) (20423/8000 : ℚ) (by norm_num) (by norm_num)
    node_459 node_462

theorem node_464 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/2000 : ℚ) (76979/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_465 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (76979/32000 : ℚ) (1571/640 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_466 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/2000 : ℚ) (1571/640 : ℚ)) := by
  exact planeBox_split_one (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/2000 : ℚ) (76979/32000 : ℚ) (1571/640 : ℚ) (by norm_num) (by norm_num)
    node_464 node_465

theorem node_467 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (4713/2000 : ℚ) (76979/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_468 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (76979/32000 : ℚ) (1571/640 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_469 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (4713/2000 : ℚ) (1571/640 : ℚ)) := by
  exact planeBox_split_one (17281/32000 : ℚ) (4713/8000 : ℚ) (4713/2000 : ℚ) (76979/32000 : ℚ) (1571/640 : ℚ) (by norm_num) (by norm_num)
    node_467 node_468

theorem node_470 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (4713/2000 : ℚ) (1571/640 : ℚ)) := by
  exact planeBox_split_zero (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (4713/2000 : ℚ) (1571/640 : ℚ) (by norm_num) (by norm_num)
    node_466 node_469

theorem node_471 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (1571/640 : ℚ) (20423/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_472 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (1571/640 : ℚ) (80121/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_473 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (80121/32000 : ℚ) (20423/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_474 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (1571/640 : ℚ) (20423/8000 : ℚ)) := by
  exact planeBox_split_one (17281/32000 : ℚ) (4713/8000 : ℚ) (1571/640 : ℚ) (80121/32000 : ℚ) (20423/8000 : ℚ) (by norm_num) (by norm_num)
    node_472 node_473

theorem node_475 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/640 : ℚ) (20423/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (1571/640 : ℚ) (20423/8000 : ℚ) (by norm_num) (by norm_num)
    node_471 node_474

theorem node_476 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (4713/2000 : ℚ) (20423/8000 : ℚ)) := by
  exact planeBox_split_one (1571/3200 : ℚ) (4713/8000 : ℚ) (4713/2000 : ℚ) (1571/640 : ℚ) (20423/8000 : ℚ) (by norm_num) (by norm_num)
    node_470 node_475

theorem node_477 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (4713/2000 : ℚ) (20423/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (4713/2000 : ℚ) (20423/8000 : ℚ) (by norm_num) (by norm_num)
    node_463 node_476

theorem node_478 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (20423/8000 : ℚ) (42417/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_479 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (42417/16000 : ℚ) (10997/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_480 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (20423/8000 : ℚ) (10997/4000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (1571/3200 : ℚ) (20423/8000 : ℚ) (42417/16000 : ℚ) (10997/4000 : ℚ) (by norm_num) (by norm_num)
    node_478 node_479

theorem node_481 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (20423/8000 : ℚ) (42417/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_482 : Certificate fc_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (20423/8000 : ℚ) (42417/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_483 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (20423/8000 : ℚ) (42417/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (20423/8000 : ℚ) (42417/16000 : ℚ) (by norm_num) (by norm_num)
    node_481 node_482

theorem node_484 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (42417/16000 : ℚ) (10997/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_485 : Certificate fc_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (20423/8000 : ℚ) (10997/4000 : ℚ)) := by
  exact planeBox_split_one (1571/3200 : ℚ) (4713/8000 : ℚ) (20423/8000 : ℚ) (42417/16000 : ℚ) (10997/4000 : ℚ) (by norm_num) (by norm_num)
    node_483 node_484

theorem node_486 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (20423/8000 : ℚ) (10997/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (20423/8000 : ℚ) (10997/4000 : ℚ) (by norm_num) (by norm_num)
    node_480 node_485

theorem node_487 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (4713/2000 : ℚ) (10997/4000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (4713/8000 : ℚ) (4713/2000 : ℚ) (20423/8000 : ℚ) (10997/4000 : ℚ) (by norm_num) (by norm_num)
    node_477 node_486

theorem node_488 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (4713/2000 : ℚ) (76979/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_489 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (76979/32000 : ℚ) (1571/640 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_490 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (4713/2000 : ℚ) (1571/640 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (20423/32000 : ℚ) (4713/2000 : ℚ) (76979/32000 : ℚ) (1571/640 : ℚ) (by norm_num) (by norm_num)
    node_488 node_489

theorem node_491 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (4713/2000 : ℚ) (76979/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_492 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (76979/32000 : ℚ) (1571/640 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_493 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (4713/2000 : ℚ) (1571/640 : ℚ)) := by
  exact planeBox_split_one (20423/32000 : ℚ) (10997/16000 : ℚ) (4713/2000 : ℚ) (76979/32000 : ℚ) (1571/640 : ℚ) (by norm_num) (by norm_num)
    node_491 node_492

theorem node_494 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (4713/2000 : ℚ) (1571/640 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (4713/2000 : ℚ) (1571/640 : ℚ) (by norm_num) (by norm_num)
    node_490 node_493

theorem node_495 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (1571/640 : ℚ) (80121/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_496 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (80121/32000 : ℚ) (20423/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_497 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (1571/640 : ℚ) (20423/8000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (20423/32000 : ℚ) (1571/640 : ℚ) (80121/32000 : ℚ) (20423/8000 : ℚ) (by norm_num) (by norm_num)
    node_495 node_496

theorem node_498 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (1571/640 : ℚ) (80121/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_499 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (80121/32000 : ℚ) (20423/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_500 : Certificate fc_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (1571/640 : ℚ) (20423/8000 : ℚ)) := by
  exact planeBox_split_one (20423/32000 : ℚ) (10997/16000 : ℚ) (1571/640 : ℚ) (80121/32000 : ℚ) (20423/8000 : ℚ) (by norm_num) (by norm_num)
    node_498 node_499

theorem node_501 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/640 : ℚ) (20423/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (1571/640 : ℚ) (20423/8000 : ℚ) (by norm_num) (by norm_num)
    node_497 node_500

theorem node_502 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (4713/2000 : ℚ) (20423/8000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (10997/16000 : ℚ) (4713/2000 : ℚ) (1571/640 : ℚ) (20423/8000 : ℚ) (by norm_num) (by norm_num)
    node_494 node_501

theorem node_503 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (4713/2000 : ℚ) (76979/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_504 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (76979/32000 : ℚ) (1571/640 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_505 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (4713/2000 : ℚ) (1571/640 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (4713/6400 : ℚ) (4713/2000 : ℚ) (76979/32000 : ℚ) (1571/640 : ℚ) (by norm_num) (by norm_num)
    node_503 node_504

theorem node_506 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (4713/2000 : ℚ) (76979/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_507 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (76979/32000 : ℚ) (1571/640 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_508 : Certificate fc_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (4713/2000 : ℚ) (1571/640 : ℚ)) := by
  exact planeBox_split_one (4713/6400 : ℚ) (1571/2000 : ℚ) (4713/2000 : ℚ) (76979/32000 : ℚ) (1571/640 : ℚ) (by norm_num) (by norm_num)
    node_506 node_507

theorem node_509 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/2000 : ℚ) (1571/640 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (4713/2000 : ℚ) (1571/640 : ℚ) (by norm_num) (by norm_num)
    node_505 node_508

theorem node_510 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/640 : ℚ) (20423/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_511 : Certificate fc_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/2000 : ℚ) (20423/8000 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/2000 : ℚ) (1571/640 : ℚ) (20423/8000 : ℚ) (by norm_num) (by norm_num)
    node_509 node_510

theorem node_512 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (4713/2000 : ℚ) (20423/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/2000 : ℚ) (20423/8000 : ℚ) (by norm_num) (by norm_num)
    node_502 node_511

theorem node_513 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (20423/8000 : ℚ) (10997/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_514 : Certificate fc_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (4713/2000 : ℚ) (10997/4000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (1571/2000 : ℚ) (4713/2000 : ℚ) (20423/8000 : ℚ) (10997/4000 : ℚ) (by norm_num) (by norm_num)
    node_512 node_513

theorem node_515 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (4713/2000 : ℚ) (10997/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (4713/2000 : ℚ) (10997/4000 : ℚ) (by norm_num) (by norm_num)
    node_487 node_514

theorem node_516 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (10997/4000 : ℚ) (1571/500 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_517 : Certificate fc_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (4713/2000 : ℚ) (1571/500 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (1571/2000 : ℚ) (4713/2000 : ℚ) (10997/4000 : ℚ) (1571/500 : ℚ) (by norm_num) (by norm_num)
    node_515 node_516

theorem node_518 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/2000 : ℚ) (4713/2000 : ℚ) (1571/500 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (4713/2000 : ℚ) (1571/500 : ℚ) (by norm_num) (by norm_num)
    node_456 node_517

theorem node_519 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (1571/500 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (4713/2000 : ℚ) (1571/500 : ℚ) (by norm_num) (by norm_num)
    node_423 node_518

theorem node_520 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (1571/1000 : ℚ) (51843/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_521 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (51843/32000 : ℚ) (26707/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_522 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (26707/32000 : ℚ) (1571/1000 : ℚ) (51843/32000 : ℚ) (26707/16000 : ℚ) (by norm_num) (by norm_num)
    node_520 node_521

theorem node_523 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (1571/1000 : ℚ) (51843/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_524 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (51843/32000 : ℚ) (26707/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_525 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ)) := by
  exact planeBox_split_one (26707/32000 : ℚ) (14139/16000 : ℚ) (1571/1000 : ℚ) (51843/32000 : ℚ) (26707/16000 : ℚ) (by norm_num) (by norm_num)
    node_523 node_524

theorem node_526 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ) (by norm_num) (by norm_num)
    node_522 node_525

theorem node_527 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (26707/16000 : ℚ) (10997/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_528 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (10997/6400 : ℚ) (14139/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_529 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (26707/32000 : ℚ) (26707/16000 : ℚ) (10997/6400 : ℚ) (14139/8000 : ℚ) (by norm_num) (by norm_num)
    node_527 node_528

theorem node_530 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (26707/16000 : ℚ) (10997/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_531 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (10997/6400 : ℚ) (14139/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_532 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ)) := by
  exact planeBox_split_one (26707/32000 : ℚ) (14139/16000 : ℚ) (26707/16000 : ℚ) (10997/6400 : ℚ) (14139/8000 : ℚ) (by norm_num) (by norm_num)
    node_530 node_531

theorem node_533 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ) (by norm_num) (by norm_num)
    node_529 node_532

theorem node_534 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ) (by norm_num) (by norm_num)
    node_526 node_533

theorem node_535 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1000 : ℚ) (51843/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_536 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (51843/32000 : ℚ) (26707/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_537 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1000 : ℚ) (51843/32000 : ℚ) (26707/16000 : ℚ) (by norm_num) (by norm_num)
    node_535 node_536

theorem node_538 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (1571/1000 : ℚ) (51843/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_539 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (51843/32000 : ℚ) (26707/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_540 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ)) := by
  exact planeBox_split_one (29849/32000 : ℚ) (1571/1600 : ℚ) (1571/1000 : ℚ) (51843/32000 : ℚ) (26707/16000 : ℚ) (by norm_num) (by norm_num)
    node_538 node_539

theorem node_541 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ) (by norm_num) (by norm_num)
    node_537 node_540

theorem node_542 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (26707/16000 : ℚ) (10997/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_543 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (10997/6400 : ℚ) (14139/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_544 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (29849/32000 : ℚ) (26707/16000 : ℚ) (10997/6400 : ℚ) (14139/8000 : ℚ) (by norm_num) (by norm_num)
    node_542 node_543

theorem node_545 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (26707/16000 : ℚ) (10997/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_546 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (10997/6400 : ℚ) (14139/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_547 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ)) := by
  exact planeBox_split_one (29849/32000 : ℚ) (1571/1600 : ℚ) (26707/16000 : ℚ) (10997/6400 : ℚ) (14139/8000 : ℚ) (by norm_num) (by norm_num)
    node_545 node_546

theorem node_548 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ) (by norm_num) (by norm_num)
    node_544 node_547

theorem node_549 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ) (by norm_num) (by norm_num)
    node_541 node_548

theorem node_550 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ) (by norm_num) (by norm_num)
    node_534 node_549

theorem node_551 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/8000 : ℚ) (58127/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_552 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (58127/32000 : ℚ) (29849/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_553 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/8000 : ℚ) (58127/32000 : ℚ) (29849/16000 : ℚ) (by norm_num) (by norm_num)
    node_551 node_552

theorem node_554 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (14139/8000 : ℚ) (58127/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_555 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (58127/32000 : ℚ) (29849/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_556 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ)) := by
  exact planeBox_split_one (26707/32000 : ℚ) (14139/16000 : ℚ) (14139/8000 : ℚ) (58127/32000 : ℚ) (29849/16000 : ℚ) (by norm_num) (by norm_num)
    node_554 node_555

theorem node_557 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ) (by norm_num) (by norm_num)
    node_553 node_556

theorem node_558 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (29849/16000 : ℚ) (61269/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_559 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (61269/32000 : ℚ) (1571/800 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_560 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (26707/32000 : ℚ) (29849/16000 : ℚ) (61269/32000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_558 node_559

theorem node_561 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (29849/16000 : ℚ) (61269/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_562 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (61269/32000 : ℚ) (1571/800 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_563 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (26707/32000 : ℚ) (14139/16000 : ℚ) (29849/16000 : ℚ) (61269/32000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_561 node_562

theorem node_564 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_560 node_563

theorem node_565 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (14139/16000 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_557 node_564

theorem node_566 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (14139/8000 : ℚ) (58127/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_567 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (58127/32000 : ℚ) (29849/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_568 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (29849/32000 : ℚ) (14139/8000 : ℚ) (58127/32000 : ℚ) (29849/16000 : ℚ) (by norm_num) (by norm_num)
    node_566 node_567

theorem node_569 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_570 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ) (by norm_num) (by norm_num)
    node_568 node_569

theorem node_571 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_572 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_573 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_571 node_572

theorem node_574 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (1571/1600 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_570 node_573

theorem node_575 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_565 node_574

theorem node_576 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_550 node_575

theorem node_577 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (1571/1000 : ℚ) (51843/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_578 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (51843/32000 : ℚ) (26707/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_579 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (32991/32000 : ℚ) (1571/1000 : ℚ) (51843/32000 : ℚ) (26707/16000 : ℚ) (by norm_num) (by norm_num)
    node_577 node_578

theorem node_580 : Certificate fc_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_581 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ) (by norm_num) (by norm_num)
    node_579 node_580

theorem node_582 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_583 : Certificate fc_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_584 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ) (by norm_num) (by norm_num)
    node_582 node_583

theorem node_585 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ) (by norm_num) (by norm_num)
    node_581 node_584

theorem node_586 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_587 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_588 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (26707/16000 : ℚ) (14139/8000 : ℚ) (by norm_num) (by norm_num)
    node_586 node_587

theorem node_589 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ) (by norm_num) (by norm_num)
    node_585 node_588

theorem node_590 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_591 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_592 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (17281/16000 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_590 node_591

theorem node_593 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_594 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_595 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (4713/4000 : ℚ) (14139/8000 : ℚ) (29849/16000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_593 node_594

theorem node_596 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_592 node_595

theorem node_597 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_589 node_596

theorem node_598 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_576 node_597

theorem node_599 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_600 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_601 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ) (by norm_num) (by norm_num)
    node_599 node_600

theorem node_602 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_603 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_604 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ) (by norm_num) (by norm_num)
    node_602 node_603

theorem node_605 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ) (by norm_num) (by norm_num)
    node_601 node_604

theorem node_606 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_607 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_608 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ) (by norm_num) (by norm_num)
    node_606 node_607

theorem node_609 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_610 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_611 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ) (by norm_num) (by norm_num)
    node_609 node_610

theorem node_612 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ) (by norm_num) (by norm_num)
    node_608 node_611

theorem node_613 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ) (by norm_num) (by norm_num)
    node_605 node_612

theorem node_614 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (17281/8000 : ℚ) (14139/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_615 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/6400 : ℚ) (36133/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_616 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (26707/32000 : ℚ) (17281/8000 : ℚ) (14139/6400 : ℚ) (36133/16000 : ℚ) (by norm_num) (by norm_num)
    node_614 node_615

theorem node_617 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (17281/8000 : ℚ) (14139/6400 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_618 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (14139/6400 : ℚ) (36133/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_619 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ)) := by
  exact planeBox_split_one (26707/32000 : ℚ) (14139/16000 : ℚ) (17281/8000 : ℚ) (14139/6400 : ℚ) (36133/16000 : ℚ) (by norm_num) (by norm_num)
    node_617 node_618

theorem node_620 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ) (by norm_num) (by norm_num)
    node_616 node_619

theorem node_621 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (36133/16000 : ℚ) (73837/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_622 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (73837/32000 : ℚ) (4713/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_623 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (26707/32000 : ℚ) (36133/16000 : ℚ) (73837/32000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_621 node_622

theorem node_624 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (36133/16000 : ℚ) (73837/32000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_625 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (73837/32000 : ℚ) (4713/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_626 : Certificate fc_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (26707/32000 : ℚ) (14139/16000 : ℚ) (36133/16000 : ℚ) (73837/32000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_624 node_625

theorem node_627 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_623 node_626

theorem node_628 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (14139/16000 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_620 node_627

theorem node_629 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_630 : Certificate fc_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_631 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ) (by norm_num) (by norm_num)
    node_629 node_630

theorem node_632 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_633 : Certificate fc_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (1571/1600 : ℚ) (17281/8000 : ℚ) (36133/16000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_631 node_632

theorem node_634 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_628 node_633

theorem node_635 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_613 node_634

theorem node_636 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_637 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_638 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ) (by norm_num) (by norm_num)
    node_636 node_637

theorem node_639 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_640 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_641 : Certificate fc_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/800 : ℚ) (32991/16000 : ℚ) (17281/8000 : ℚ) (by norm_num) (by norm_num)
    node_639 node_640

theorem node_642 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ) (by norm_num) (by norm_num)
    node_638 node_641

theorem node_643 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_644 : Certificate fc_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/800 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_642 node_643

theorem node_645 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_635 node_644

theorem node_646 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_598 node_645

theorem node_647 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_648 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_649 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ) (by norm_num) (by norm_num)
    node_647 node_648

theorem node_650 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_651 : Certificate fc_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_652 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_650 node_651

theorem node_653 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_649 node_652

theorem node_654 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_655 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_656 : Certificate fc_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_one (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_654 node_655

theorem node_657 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ) (by norm_num) (by norm_num)
    node_653 node_656

theorem node_658 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_659 : Certificate fc_leaf
    (planeBox (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/1000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/1000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_657 node_658

theorem node_660 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1000 : ℚ) (1571/1000 : ℚ) (4713/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/1000 : ℚ) (4713/2000 : ℚ) (by norm_num) (by norm_num)
    node_646 node_659

theorem node_661 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1000 : ℚ) (4713/2000 : ℚ) (1571/500 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_662 : Certificate fc_leaf
    (planeBox (1571/2000 : ℚ) (1571/1000 : ℚ) (1571/1000 : ℚ) (1571/500 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (1571/1000 : ℚ) (1571/1000 : ℚ) (4713/2000 : ℚ) (1571/500 : ℚ) (by norm_num) (by norm_num)
    node_660 node_661

theorem node_663 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/1000 : ℚ) (1571/1000 : ℚ) (1571/500 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (1571/1000 : ℚ) (1571/500 : ℚ) (by norm_num) (by norm_num)
    node_519 node_662

theorem node_664 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/500 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/1000 : ℚ) (1571/500 : ℚ) (by norm_num) (by norm_num)
    node_230 node_663

theorem node_665 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (1571/800 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_666 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_667 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (14139/8000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_668 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_666 node_667

theorem node_669 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (1571/800 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_670 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (1571/800 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_671 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (1571/800 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (14139/8000 : ℚ) (1571/800 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_669 node_670

theorem node_672 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (1571/800 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_668 node_671

theorem node_673 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (1571/800 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/1000 : ℚ) (1571/800 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_665 node_672

theorem node_674 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_675 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (17281/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_676 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (17281/8000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_677 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (17281/8000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/800 : ℚ) (17281/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_675 node_676

theorem node_678 : Certificate fc_leaf
    (planeBox (17281/8000 : ℚ) (4713/2000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_679 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (4713/2000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/800 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_677 node_678

theorem node_680 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/800 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_674 node_679

theorem node_681 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/1000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_673 node_680

theorem node_682 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_683 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_684 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_682 node_683

theorem node_685 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (1571/800 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_686 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (1571/800 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_687 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (1571/800 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (14139/8000 : ℚ) (1571/800 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_685 node_686

theorem node_688 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (1571/800 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_684 node_687

theorem node_689 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (14139/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_690 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (14139/8000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_691 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (14139/8000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/1000 : ℚ) (14139/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_689 node_690

theorem node_692 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (1571/800 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_693 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (1571/800 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_694 : Certificate fc_leaf
    (planeBox (14139/8000 : ℚ) (1571/800 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (14139/8000 : ℚ) (1571/800 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_692 node_693

theorem node_695 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (1571/800 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (1571/1000 : ℚ) (14139/8000 : ℚ) (1571/800 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_691 node_694

theorem node_696 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (1571/800 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/1000 : ℚ) (1571/800 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_688 node_695

theorem node_697 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (17281/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_698 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (17281/8000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_699 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (17281/8000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/800 : ℚ) (17281/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_697 node_698

theorem node_700 : Certificate fc_leaf
    (planeBox (17281/8000 : ℚ) (4713/2000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_701 : Certificate fc_leaf
    (planeBox (17281/8000 : ℚ) (4713/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_702 : Certificate fc_leaf
    (planeBox (17281/8000 : ℚ) (4713/2000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (17281/8000 : ℚ) (4713/2000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_700 node_701

theorem node_703 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (4713/2000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/800 : ℚ) (17281/8000 : ℚ) (4713/2000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    node_699 node_702

theorem node_704 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (4713/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_705 : Certificate fc_leaf
    (planeBox (1571/800 : ℚ) (4713/2000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/800 : ℚ) (4713/2000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_703 node_704

theorem node_706 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (4713/2000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (1571/1000 : ℚ) (1571/800 : ℚ) (4713/2000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_696 node_705

theorem node_707 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/1000 : ℚ) (4713/2000 : ℚ) (0 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_681 node_706

theorem node_708 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (10997/4000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_709 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (20423/8000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_710 : Certificate fc_leaf
    (planeBox (20423/8000 : ℚ) (10997/4000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_711 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (10997/4000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (4713/2000 : ℚ) (20423/8000 : ℚ) (10997/4000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_709 node_710

theorem node_712 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (10997/4000 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (4713/2000 : ℚ) (10997/4000 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_708 node_711

theorem node_713 : Certificate fc_leaf
    (planeBox (10997/4000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inr
  norm_num [fc_p,fc_q,fc_b,fc_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem node_714 : Certificate fc_leaf
    (planeBox (10997/4000 : ℚ) (1571/500 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_715 : Certificate fc_leaf
    (planeBox (10997/4000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (10997/4000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_713 node_714

theorem node_716 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (4713/2000 : ℚ) (10997/4000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    node_712 node_715

theorem node_717 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (1571/500 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_718 : Certificate fc_leaf
    (planeBox (4713/2000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (4713/2000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_716 node_717

theorem node_719 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (1571/1000 : ℚ) (4713/2000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    node_707 node_718

theorem node_720 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (1571/500 : ℚ) (1571/1000 : ℚ) (1571/500 : ℚ)) := by
  apply Certificate.accept
  unfold fc_leaf
  apply Or.inl
  apply Or.inl
  apply Or.inl
  norm_num [PlaneOutside,planeBox,RatInterval.piHi]

theorem node_721 : Certificate fc_leaf
    (planeBox (1571/1000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/500 : ℚ)) := by
  exact planeBox_split_one (1571/1000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/1000 : ℚ) (1571/500 : ℚ) (by norm_num) (by norm_num)
    node_719 node_720

theorem node_722 : Certificate fc_leaf
    (planeBox (0 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/500 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/1000 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/500 : ℚ) (by norm_num) (by norm_num)
    node_664 node_721

/-- `EfficientFaceCertificate` for this face (FaceCertificate.plane, root as in A25 Face1). -/
def certificate : SharedMomentEfficientFactorCertificate.EfficientFaceCertificate fc_p fc_q fc_b fc_bound :=
  .base (.plane (planeBox (0 : ℚ) (1571/500 : ℚ) (0 : ℚ) (1571/500 : ℚ))
    (by intro i; fin_cases i <;> norm_num [planeBox,RatInterval.piHi]) node_722)
end N11Formalization.Class33FaceTreeQ0M2F0_9_10
#print axioms N11Formalization.Class33FaceTreeQ0M2F0_9_10.node_722
