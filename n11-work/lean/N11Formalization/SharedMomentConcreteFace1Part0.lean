import N11Formalization.SharedMomentConcreteFace1Data

set_option autoImplicit false
noncomputable section
namespace N11Formalization.SharedMomentConcreteFace1
open RationalBoxSubdivision SharedMomentFacePlaneGradientCertificate SharedMomentFacePlaneCertificate
open SharedMomentFacePlaneDirectCertificate SharedMomentFactorRationalNodes
open SharedMomentFactorIntervalCertificate SharedMomentFactorLocalGradientCertificate
open RationalTrigLocalLipschitz

theorem start0_face1_node_0 : Certificate start0_face1_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inl
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_1 : Certificate start0_face1_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inl
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_2 : Certificate start0_face1_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_0 start0_face1_node_1

theorem start0_face1_node_3 : Certificate start0_face1_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inl
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_4 : Certificate start0_face1_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_5 : Certificate start0_face1_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_3 start0_face1_node_4

theorem start0_face1_node_6 : Certificate start0_face1_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_7 : Certificate start0_face1_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_8 : Certificate start0_face1_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_6 start0_face1_node_7

theorem start0_face1_node_9 : Certificate start0_face1_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_5 start0_face1_node_8

theorem start0_face1_node_10 : Certificate start0_face1_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/4000 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_2 start0_face1_node_9

theorem start0_face1_node_11 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inl
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_12 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inl
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_13 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (4713/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_11 start0_face1_node_12

theorem start0_face1_node_14 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inl
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_15 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inl
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_16 : Certificate start0_face1_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inl
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_17 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_15 start0_face1_node_16

theorem start0_face1_node_18 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_14 start0_face1_node_17

theorem start0_face1_node_19 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_13 start0_face1_node_18

theorem start0_face1_node_20 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inl
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_21 : Certificate start0_face1_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inl
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_22 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_20 start0_face1_node_21

theorem start0_face1_node_23 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_24 : Certificate start0_face1_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_25 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_23 start0_face1_node_24

theorem start0_face1_node_26 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_22 start0_face1_node_25

theorem start0_face1_node_27 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inl
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_28 : Certificate start0_face1_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inl
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_29 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_27 start0_face1_node_28

theorem start0_face1_node_30 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_31 : Certificate start0_face1_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_32 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_30 start0_face1_node_31

theorem start0_face1_node_33 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_29 start0_face1_node_32

theorem start0_face1_node_34 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_26 start0_face1_node_33

theorem start0_face1_node_35 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_19 start0_face1_node_34

theorem start0_face1_node_36 : Certificate start0_face1_leaf
    (planeBox (0 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_10 start0_face1_node_35

theorem start0_face1_node_37 : Certificate start0_face1_leaf
    (planeBox (0 : ℚ) (1571/16000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_38 : Certificate start0_face1_leaf
    (planeBox (1571/16000 : ℚ) (1571/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_39 : Certificate start0_face1_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_37 start0_face1_node_38

theorem start0_face1_node_40 : Certificate start0_face1_leaf
    (planeBox (0 : ℚ) (1571/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_41 : Certificate start0_face1_leaf
    (planeBox (1571/16000 : ℚ) (1571/8000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_42 : Certificate start0_face1_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_40 start0_face1_node_41

theorem start0_face1_node_43 : Certificate start0_face1_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_39 start0_face1_node_42

theorem start0_face1_node_44 : Certificate start0_face1_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_45 : Certificate start0_face1_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_46 : Certificate start0_face1_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_44 start0_face1_node_45

theorem start0_face1_node_47 : Certificate start0_face1_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_48 : Certificate start0_face1_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_49 : Certificate start0_face1_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_47 start0_face1_node_48

theorem start0_face1_node_50 : Certificate start0_face1_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_46 start0_face1_node_49

theorem start0_face1_node_51 : Certificate start0_face1_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_43 start0_face1_node_50

theorem start0_face1_node_52 : Certificate start0_face1_leaf
    (planeBox (0 : ℚ) (1571/16000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_53 : Certificate start0_face1_leaf
    (planeBox (1571/16000 : ℚ) (1571/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_54 : Certificate start0_face1_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_52 start0_face1_node_53

theorem start0_face1_node_55 : Certificate start0_face1_leaf
    (planeBox (0 : ℚ) (1571/16000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_56 : Certificate start0_face1_leaf
    (planeBox (1571/16000 : ℚ) (1571/8000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_57 : Certificate start0_face1_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_55 start0_face1_node_56

theorem start0_face1_node_58 : Certificate start0_face1_leaf
    (planeBox (0 : ℚ) (1571/8000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_54 start0_face1_node_57

theorem start0_face1_node_59 : Certificate start0_face1_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_60 : Certificate start0_face1_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_61 : Certificate start0_face1_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_59 start0_face1_node_60

theorem start0_face1_node_62 : Certificate start0_face1_leaf
    (planeBox (1571/8000 : ℚ) (4713/16000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_63 : Certificate start0_face1_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_64 : Certificate start0_face1_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_65 : Certificate start0_face1_leaf
    (planeBox (4713/16000 : ℚ) (1571/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (4713/16000 : ℚ) (1571/4000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_63 start0_face1_node_64

theorem start0_face1_node_66 : Certificate start0_face1_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_62 start0_face1_node_65

theorem start0_face1_node_67 : Certificate start0_face1_leaf
    (planeBox (1571/8000 : ℚ) (1571/4000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/8000 : ℚ) (1571/4000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_61 start0_face1_node_66

theorem start0_face1_node_68 : Certificate start0_face1_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_58 start0_face1_node_67

theorem start0_face1_node_69 : Certificate start0_face1_leaf
    (planeBox (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_51 start0_face1_node_68

theorem start0_face1_node_70 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_71 : Certificate start0_face1_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_72 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_70 start0_face1_node_71

theorem start0_face1_node_73 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_74 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_75 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (1571/3200 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_73 start0_face1_node_74

theorem start0_face1_node_76 : Certificate start0_face1_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_77 : Certificate start0_face1_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_78 : Certificate start0_face1_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_76 start0_face1_node_77

theorem start0_face1_node_79 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_75 start0_face1_node_78

theorem start0_face1_node_80 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_72 start0_face1_node_79

theorem start0_face1_node_81 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_82 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_83 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_81 start0_face1_node_82

theorem start0_face1_node_84 : Certificate start0_face1_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_85 : Certificate start0_face1_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_86 : Certificate start0_face1_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_87 : Certificate start0_face1_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_85 start0_face1_node_86

theorem start0_face1_node_88 : Certificate start0_face1_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_84 start0_face1_node_87

theorem start0_face1_node_89 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_83 start0_face1_node_88

theorem start0_face1_node_90 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_91 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_92 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_90 start0_face1_node_91

theorem start0_face1_node_93 : Certificate start0_face1_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_94 : Certificate start0_face1_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_95 : Certificate start0_face1_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_93 start0_face1_node_94

theorem start0_face1_node_96 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_92 start0_face1_node_95

theorem start0_face1_node_97 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_89 start0_face1_node_96

theorem start0_face1_node_98 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_80 start0_face1_node_97

theorem start0_face1_node_99 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_100 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_101 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_99 start0_face1_node_100

theorem start0_face1_node_102 : Certificate start0_face1_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_103 : Certificate start0_face1_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_104 : Certificate start0_face1_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (1571/3200 : ℚ) (4713/8000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_102 start0_face1_node_103

theorem start0_face1_node_105 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_101 start0_face1_node_104

theorem start0_face1_node_106 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_107 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_108 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (1571/3200 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (1571/3200 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_106 start0_face1_node_107

theorem start0_face1_node_109 : Certificate start0_face1_leaf
    (planeBox (1571/3200 : ℚ) (17281/32000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_110 : Certificate start0_face1_leaf
    (planeBox (17281/32000 : ℚ) (4713/8000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_111 : Certificate start0_face1_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  exact planeBox_split_zero (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_109 start0_face1_node_110

theorem start0_face1_node_112 : Certificate start0_face1_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_113 : Certificate start0_face1_leaf
    (planeBox (1571/3200 : ℚ) (4713/8000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/3200 : ℚ) (4713/8000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_111 start0_face1_node_112

theorem start0_face1_node_114 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_108 start0_face1_node_113

theorem start0_face1_node_115 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (4713/8000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (4713/8000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_105 start0_face1_node_114

theorem start0_face1_node_116 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_117 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_118 : Certificate start0_face1_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_119 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_117 start0_face1_node_118

theorem start0_face1_node_120 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (10997/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_116 start0_face1_node_119

theorem start0_face1_node_121 : Certificate start0_face1_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_122 : Certificate start0_face1_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_123 : Certificate start0_face1_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_121 start0_face1_node_122

theorem start0_face1_node_124 : Certificate start0_face1_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_125 : Certificate start0_face1_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_126 : Certificate start0_face1_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_124 start0_face1_node_125

theorem start0_face1_node_127 : Certificate start0_face1_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_123 start0_face1_node_126

theorem start0_face1_node_128 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_120 start0_face1_node_127

theorem start0_face1_node_129 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_130 : Certificate start0_face1_leaf
    (planeBox (20423/32000 : ℚ) (10997/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_131 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_129 start0_face1_node_130

theorem start0_face1_node_132 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_133 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (10997/16000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (10997/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_131 start0_face1_node_132

theorem start0_face1_node_134 : Certificate start0_face1_leaf
    (planeBox (10997/16000 : ℚ) (4713/6400 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_135 : Certificate start0_face1_leaf
    (planeBox (4713/6400 : ℚ) (1571/2000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_136 : Certificate start0_face1_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  exact planeBox_split_zero (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_134 start0_face1_node_135

theorem start0_face1_node_137 : Certificate start0_face1_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_138 : Certificate start0_face1_leaf
    (planeBox (10997/16000 : ℚ) (1571/2000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (10997/16000 : ℚ) (1571/2000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_136 start0_face1_node_137

theorem start0_face1_node_139 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_133 start0_face1_node_138

theorem start0_face1_node_140 : Certificate start0_face1_leaf
    (planeBox (4713/8000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (4713/8000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_128 start0_face1_node_139

theorem start0_face1_node_141 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_115 start0_face1_node_140

theorem start0_face1_node_142 : Certificate start0_face1_leaf
    (planeBox (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_98 start0_face1_node_141

theorem start0_face1_node_143 : Certificate start0_face1_leaf
    (planeBox (0 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_69 start0_face1_node_142

theorem start0_face1_node_144 : Certificate start0_face1_leaf
    (planeBox (0 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (0 : ℚ) (1571/2000 : ℚ) (0 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_36 start0_face1_node_143

theorem start0_face1_node_145 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inl
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_146 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inl
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_147 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inl
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_148 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_146 start0_face1_node_147

theorem start0_face1_node_149 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (1571/1600 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_145 start0_face1_node_148

theorem start0_face1_node_150 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inl
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_151 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inl
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_152 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_150 start0_face1_node_151

theorem start0_face1_node_153 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inl
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_154 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inl
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_155 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_153 start0_face1_node_154

theorem start0_face1_node_156 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (4713/4000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_152 start0_face1_node_155

theorem start0_face1_node_157 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (4713/4000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_149 start0_face1_node_156

theorem start0_face1_node_158 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_159 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_160 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_158 start0_face1_node_159

theorem start0_face1_node_161 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_162 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_163 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (14139/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_161 start0_face1_node_162

theorem start0_face1_node_164 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_165 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_166 : Certificate start0_face1_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_167 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_165 start0_face1_node_166

theorem start0_face1_node_168 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_164 start0_face1_node_167

theorem start0_face1_node_169 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_163 start0_face1_node_168

theorem start0_face1_node_170 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_160 start0_face1_node_169

theorem start0_face1_node_171 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_172 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_173 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_174 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_172 start0_face1_node_173

theorem start0_face1_node_175 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_171 start0_face1_node_174

theorem start0_face1_node_176 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_177 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_178 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_179 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_177 start0_face1_node_178

theorem start0_face1_node_180 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_176 start0_face1_node_179

theorem start0_face1_node_181 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_182 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_183 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_181 start0_face1_node_182

theorem start0_face1_node_184 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_185 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_186 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_187 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (36133/32000 : ℚ) (4713/4000 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_185 start0_face1_node_186

theorem start0_face1_node_188 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_184 start0_face1_node_187

theorem start0_face1_node_189 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (4713/4000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_183 start0_face1_node_188

theorem start0_face1_node_190 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_180 start0_face1_node_189

theorem start0_face1_node_191 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_175 start0_face1_node_190

theorem start0_face1_node_192 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_170 start0_face1_node_191

theorem start0_face1_node_193 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (4713/4000 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (4713/4000 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_157 start0_face1_node_192

theorem start0_face1_node_194 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inl
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_195 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_196 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (10997/8000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_194 start0_face1_node_195

theorem start0_face1_node_197 : Certificate start0_face1_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inl
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_198 : Certificate start0_face1_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_199 : Certificate start0_face1_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_one (10997/8000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_197 start0_face1_node_198

theorem start0_face1_node_200 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/4000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_196 start0_face1_node_199

theorem start0_face1_node_201 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_202 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_203 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (20423/16000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_201 start0_face1_node_202

theorem start0_face1_node_204 : Certificate start0_face1_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_205 : Certificate start0_face1_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_206 : Certificate start0_face1_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_204 start0_face1_node_205

theorem start0_face1_node_207 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_203 start0_face1_node_206

theorem start0_face1_node_208 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (1571/1280 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_209 : Certificate start0_face1_leaf
    (planeBox (1571/1280 : ℚ) (20423/16000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_210 : Certificate start0_face1_leaf
    (planeBox (1571/1280 : ℚ) (20423/16000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_211 : Certificate start0_face1_leaf
    (planeBox (1571/1280 : ℚ) (20423/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_one (1571/1280 : ℚ) (20423/16000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_209 start0_face1_node_210

theorem start0_face1_node_212 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (1571/1280 : ℚ) (20423/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_208 start0_face1_node_211

theorem start0_face1_node_213 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (1571/1280 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_214 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (1571/1280 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_215 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (1571/1280 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (1571/1280 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_213 start0_face1_node_214

theorem start0_face1_node_216 : Certificate start0_face1_leaf
    (planeBox (1571/1280 : ℚ) (20423/16000 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_217 : Certificate start0_face1_leaf
    (planeBox (1571/1280 : ℚ) (20423/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_218 : Certificate start0_face1_leaf
    (planeBox (1571/1280 : ℚ) (20423/16000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (1571/1280 : ℚ) (20423/16000 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_216 start0_face1_node_217

theorem start0_face1_node_219 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (1571/1280 : ℚ) (20423/16000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_215 start0_face1_node_218

theorem start0_face1_node_220 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (20423/16000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_212 start0_face1_node_219

theorem start0_face1_node_221 : Certificate start0_face1_leaf
    (planeBox (20423/16000 : ℚ) (42417/32000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_222 : Certificate start0_face1_leaf
    (planeBox (20423/16000 : ℚ) (42417/32000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_223 : Certificate start0_face1_leaf
    (planeBox (20423/16000 : ℚ) (42417/32000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_one (20423/16000 : ℚ) (42417/32000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_221 start0_face1_node_222

theorem start0_face1_node_224 : Certificate start0_face1_leaf
    (planeBox (42417/32000 : ℚ) (10997/8000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_225 : Certificate start0_face1_leaf
    (planeBox (42417/32000 : ℚ) (10997/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_226 : Certificate start0_face1_leaf
    (planeBox (42417/32000 : ℚ) (10997/8000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_one (42417/32000 : ℚ) (10997/8000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_224 start0_face1_node_225

theorem start0_face1_node_227 : Certificate start0_face1_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_zero (20423/16000 : ℚ) (42417/32000 : ℚ) (10997/8000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_223 start0_face1_node_226

theorem start0_face1_node_228 : Certificate start0_face1_leaf
    (planeBox (20423/16000 : ℚ) (42417/32000 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_229 : Certificate start0_face1_leaf
    (planeBox (20423/16000 : ℚ) (42417/32000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_230 : Certificate start0_face1_leaf
    (planeBox (20423/16000 : ℚ) (42417/32000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (20423/16000 : ℚ) (42417/32000 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_228 start0_face1_node_229

theorem start0_face1_node_231 : Certificate start0_face1_leaf
    (planeBox (42417/32000 : ℚ) (10997/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_232 : Certificate start0_face1_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (20423/16000 : ℚ) (42417/32000 : ℚ) (10997/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_230 start0_face1_node_231

theorem start0_face1_node_233 : Certificate start0_face1_leaf
    (planeBox (20423/16000 : ℚ) (10997/8000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (20423/16000 : ℚ) (10997/8000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_227 start0_face1_node_232

theorem start0_face1_node_234 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_220 start0_face1_node_233

theorem start0_face1_node_235 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_207 start0_face1_node_234

theorem start0_face1_node_236 : Certificate start0_face1_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_237 : Certificate start0_face1_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_238 : Certificate start0_face1_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_236 start0_face1_node_237

theorem start0_face1_node_239 : Certificate start0_face1_leaf
    (planeBox (4713/3200 : ℚ) (1571/1000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_240 : Certificate start0_face1_leaf
    (planeBox (4713/3200 : ℚ) (1571/1000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_241 : Certificate start0_face1_leaf
    (planeBox (4713/3200 : ℚ) (1571/1000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_one (4713/3200 : ℚ) (1571/1000 : ℚ) (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_239 start0_face1_node_240

theorem start0_face1_node_242 : Certificate start0_face1_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact planeBox_split_zero (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_238 start0_face1_node_241

theorem start0_face1_node_243 : Certificate start0_face1_leaf
    (planeBox (10997/8000 : ℚ) (45559/32000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_244 : Certificate start0_face1_leaf
    (planeBox (10997/8000 : ℚ) (45559/32000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_245 : Certificate start0_face1_leaf
    (planeBox (10997/8000 : ℚ) (45559/32000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_one (10997/8000 : ℚ) (45559/32000 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_243 start0_face1_node_244

theorem start0_face1_node_246 : Certificate start0_face1_leaf
    (planeBox (45559/32000 : ℚ) (4713/3200 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_247 : Certificate start0_face1_leaf
    (planeBox (45559/32000 : ℚ) (4713/3200 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_248 : Certificate start0_face1_leaf
    (planeBox (45559/32000 : ℚ) (4713/3200 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_one (45559/32000 : ℚ) (4713/3200 : ℚ) (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_246 start0_face1_node_247

theorem start0_face1_node_249 : Certificate start0_face1_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_zero (10997/8000 : ℚ) (45559/32000 : ℚ) (4713/3200 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_245 start0_face1_node_248

theorem start0_face1_node_250 : Certificate start0_face1_leaf
    (planeBox (10997/8000 : ℚ) (45559/32000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_251 : Certificate start0_face1_leaf
    (planeBox (45559/32000 : ℚ) (4713/3200 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_252 : Certificate start0_face1_leaf
    (planeBox (45559/32000 : ℚ) (4713/3200 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_253 : Certificate start0_face1_leaf
    (planeBox (45559/32000 : ℚ) (4713/3200 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (45559/32000 : ℚ) (4713/3200 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_251 start0_face1_node_252

theorem start0_face1_node_254 : Certificate start0_face1_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (10997/8000 : ℚ) (45559/32000 : ℚ) (4713/3200 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_250 start0_face1_node_253

theorem start0_face1_node_255 : Certificate start0_face1_leaf
    (planeBox (10997/8000 : ℚ) (4713/3200 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (10997/8000 : ℚ) (4713/3200 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_249 start0_face1_node_254

theorem start0_face1_node_256 : Certificate start0_face1_leaf
    (planeBox (4713/3200 : ℚ) (48701/32000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_257 : Certificate start0_face1_leaf
    (planeBox (48701/32000 : ℚ) (1571/1000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_258 : Certificate start0_face1_leaf
    (planeBox (4713/3200 : ℚ) (1571/1000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact planeBox_split_zero (4713/3200 : ℚ) (48701/32000 : ℚ) (1571/1000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_256 start0_face1_node_257

theorem start0_face1_node_259 : Certificate start0_face1_leaf
    (planeBox (4713/3200 : ℚ) (48701/32000 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_260 : Certificate start0_face1_leaf
    (planeBox (4713/3200 : ℚ) (48701/32000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_261 : Certificate start0_face1_leaf
    (planeBox (4713/3200 : ℚ) (48701/32000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (4713/3200 : ℚ) (48701/32000 : ℚ) (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_259 start0_face1_node_260

theorem start0_face1_node_262 : Certificate start0_face1_leaf
    (planeBox (48701/32000 : ℚ) (1571/1000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_263 : Certificate start0_face1_leaf
    (planeBox (4713/3200 : ℚ) (1571/1000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (4713/3200 : ℚ) (48701/32000 : ℚ) (1571/1000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_261 start0_face1_node_262

theorem start0_face1_node_264 : Certificate start0_face1_leaf
    (planeBox (4713/3200 : ℚ) (1571/1000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (4713/3200 : ℚ) (1571/1000 : ℚ) (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_258 start0_face1_node_263

theorem start0_face1_node_265 : Certificate start0_face1_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_255 start0_face1_node_264

theorem start0_face1_node_266 : Certificate start0_face1_leaf
    (planeBox (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_242 start0_face1_node_265

theorem start0_face1_node_267 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (1571/1000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_235 start0_face1_node_266

theorem start0_face1_node_268 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_200 start0_face1_node_267

theorem start0_face1_node_269 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/2000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (0 : ℚ) (1571/2000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_193 start0_face1_node_268

theorem start0_face1_node_270 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_271 : Certificate start0_face1_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_272 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_270 start0_face1_node_271

theorem start0_face1_node_273 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_274 : Certificate start0_face1_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_275 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_273 start0_face1_node_274

theorem start0_face1_node_276 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_272 start0_face1_node_275

theorem start0_face1_node_277 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_278 : Certificate start0_face1_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_279 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_277 start0_face1_node_278

theorem start0_face1_node_280 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_281 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_282 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (29849/32000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_280 start0_face1_node_281

theorem start0_face1_node_283 : Certificate start0_face1_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_284 : Certificate start0_face1_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_285 : Certificate start0_face1_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (29849/32000 : ℚ) (1571/1600 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_283 start0_face1_node_284

theorem start0_face1_node_286 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_282 start0_face1_node_285

theorem start0_face1_node_287 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_279 start0_face1_node_286

theorem start0_face1_node_288 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_276 start0_face1_node_287

theorem start0_face1_node_289 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_290 : Certificate start0_face1_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_291 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_289 start0_face1_node_290

theorem start0_face1_node_292 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_293 : Certificate start0_face1_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_294 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_292 start0_face1_node_293

theorem start0_face1_node_295 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_291 start0_face1_node_294

theorem start0_face1_node_296 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_297 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_298 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_296 start0_face1_node_297

theorem start0_face1_node_299 : Certificate start0_face1_leaf
    (planeBox (29849/32000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_300 : Certificate start0_face1_leaf
    (planeBox (61269/64000 : ℚ) (1571/1600 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_301 : Certificate start0_face1_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ)) := by
  exact planeBox_split_zero (29849/32000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_299 start0_face1_node_300

theorem start0_face1_node_302 : Certificate start0_face1_leaf
    (planeBox (29849/32000 : ℚ) (61269/64000 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_303 : Certificate start0_face1_leaf
    (planeBox (61269/64000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_304 : Certificate start0_face1_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_zero (29849/32000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_302 start0_face1_node_303

theorem start0_face1_node_305 : Certificate start0_face1_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_one (29849/32000 : ℚ) (1571/1600 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_301 start0_face1_node_304

theorem start0_face1_node_306 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_298 start0_face1_node_305

theorem start0_face1_node_307 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_308 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_309 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (29849/32000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_307 start0_face1_node_308

theorem start0_face1_node_310 : Certificate start0_face1_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_311 : Certificate start0_face1_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_312 : Certificate start0_face1_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (29849/32000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_310 start0_face1_node_311

theorem start0_face1_node_313 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_309 start0_face1_node_312

theorem start0_face1_node_314 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_306 start0_face1_node_313

theorem start0_face1_node_315 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_295 start0_face1_node_314

theorem start0_face1_node_316 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (1571/1600 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_288 start0_face1_node_315

theorem start0_face1_node_317 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_318 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_319 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (32991/32000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_317 start0_face1_node_318

theorem start0_face1_node_320 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_321 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (67553/64000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_322 : Certificate start0_face1_leaf
    (planeBox (67553/64000 : ℚ) (17281/16000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_323 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_zero (32991/32000 : ℚ) (67553/64000 : ℚ) (17281/16000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_321 start0_face1_node_322

theorem start0_face1_node_324 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_one (32991/32000 : ℚ) (17281/16000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_320 start0_face1_node_323

theorem start0_face1_node_325 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_319 start0_face1_node_324

theorem start0_face1_node_326 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (64411/64000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_327 : Certificate start0_face1_leaf
    (planeBox (64411/64000 : ℚ) (32991/32000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_328 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_326 start0_face1_node_327

theorem start0_face1_node_329 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (64411/64000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_330 : Certificate start0_face1_leaf
    (planeBox (64411/64000 : ℚ) (32991/32000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_331 : Certificate start0_face1_leaf
    (planeBox (64411/64000 : ℚ) (32991/32000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_332 : Certificate start0_face1_leaf
    (planeBox (64411/64000 : ℚ) (32991/32000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (64411/64000 : ℚ) (32991/32000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_330 start0_face1_node_331

theorem start0_face1_node_333 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_329 start0_face1_node_332

theorem start0_face1_node_334 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (32991/32000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_328 start0_face1_node_333

theorem start0_face1_node_335 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (67553/64000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_336 : Certificate start0_face1_leaf
    (planeBox (67553/64000 : ℚ) (17281/16000 : ℚ) (14139/16000 : ℚ) (58127/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_337 : Certificate start0_face1_leaf
    (planeBox (67553/64000 : ℚ) (17281/16000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_338 : Certificate start0_face1_leaf
    (planeBox (67553/64000 : ℚ) (17281/16000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_one (67553/64000 : ℚ) (17281/16000 : ℚ) (14139/16000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_336 start0_face1_node_337

theorem start0_face1_node_339 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_zero (32991/32000 : ℚ) (67553/64000 : ℚ) (17281/16000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_335 start0_face1_node_338

theorem start0_face1_node_340 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (67553/64000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_341 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (67553/64000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_342 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (67553/64000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (32991/32000 : ℚ) (67553/64000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_340 start0_face1_node_341

theorem start0_face1_node_343 : Certificate start0_face1_leaf
    (planeBox (67553/64000 : ℚ) (136677/128000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_344 : Certificate start0_face1_leaf
    (planeBox (136677/128000 : ℚ) (17281/16000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_345 : Certificate start0_face1_leaf
    (planeBox (67553/64000 : ℚ) (17281/16000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ)) := by
  exact planeBox_split_zero (67553/64000 : ℚ) (136677/128000 : ℚ) (17281/16000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_343 start0_face1_node_344

theorem start0_face1_node_346 : Certificate start0_face1_leaf
    (planeBox (67553/64000 : ℚ) (136677/128000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_347 : Certificate start0_face1_leaf
    (planeBox (136677/128000 : ℚ) (17281/16000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_348 : Certificate start0_face1_leaf
    (planeBox (67553/64000 : ℚ) (17281/16000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (67553/64000 : ℚ) (136677/128000 : ℚ) (17281/16000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_346 start0_face1_node_347

theorem start0_face1_node_349 : Certificate start0_face1_leaf
    (planeBox (67553/64000 : ℚ) (17281/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (67553/64000 : ℚ) (17281/16000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_345 start0_face1_node_348

theorem start0_face1_node_350 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (32991/32000 : ℚ) (67553/64000 : ℚ) (17281/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_342 start0_face1_node_349

theorem start0_face1_node_351 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (32991/32000 : ℚ) (17281/16000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_339 start0_face1_node_350

theorem start0_face1_node_352 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_334 start0_face1_node_351

theorem start0_face1_node_353 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_325 start0_face1_node_352

theorem start0_face1_node_354 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_355 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (14139/12800 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_356 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (36133/32000 : ℚ) (26707/32000 : ℚ) (10997/12800 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_357 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (36133/32000 : ℚ) (10997/12800 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_358 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (36133/32000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_one (14139/12800 : ℚ) (36133/32000 : ℚ) (26707/32000 : ℚ) (10997/12800 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_356 start0_face1_node_357

theorem start0_face1_node_359 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (14139/12800 : ℚ) (36133/32000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_355 start0_face1_node_358

theorem start0_face1_node_360 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (36133/32000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_354 start0_face1_node_359

theorem start0_face1_node_361 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (73837/64000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_362 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_363 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ)) := by
  exact planeBox_split_zero (36133/32000 : ℚ) (73837/64000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_361 start0_face1_node_362

theorem start0_face1_node_364 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (73837/64000 : ℚ) (26707/32000 : ℚ) (10997/12800 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_365 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (73837/64000 : ℚ) (10997/12800 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_366 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (73837/64000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_one (36133/32000 : ℚ) (73837/64000 : ℚ) (26707/32000 : ℚ) (10997/12800 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_364 start0_face1_node_365

theorem start0_face1_node_367 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (4713/4000 : ℚ) (26707/32000 : ℚ) (10997/12800 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_368 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (4713/4000 : ℚ) (10997/12800 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_369 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (4713/4000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_one (73837/64000 : ℚ) (4713/4000 : ℚ) (26707/32000 : ℚ) (10997/12800 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_367 start0_face1_node_368

theorem start0_face1_node_370 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_zero (36133/32000 : ℚ) (73837/64000 : ℚ) (4713/4000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_366 start0_face1_node_369

theorem start0_face1_node_371 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_one (36133/32000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_363 start0_face1_node_370

theorem start0_face1_node_372 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_360 start0_face1_node_371

theorem start0_face1_node_373 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (14139/12800 : ℚ) (14139/16000 : ℚ) (58127/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_374 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (139819/128000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_375 : Certificate start0_face1_leaf
    (planeBox (139819/128000 : ℚ) (14139/12800 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_376 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (14139/12800 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (139819/128000 : ℚ) (14139/12800 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_374 start0_face1_node_375

theorem start0_face1_node_377 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (14139/12800 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (14139/12800 : ℚ) (14139/16000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_373 start0_face1_node_376

theorem start0_face1_node_378 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (36133/32000 : ℚ) (14139/16000 : ℚ) (58127/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_379 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (142961/128000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_380 : Certificate start0_face1_leaf
    (planeBox (142961/128000 : ℚ) (36133/32000 : ℚ) (58127/64000 : ℚ) (4713/5120 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_381 : Certificate start0_face1_leaf
    (planeBox (142961/128000 : ℚ) (36133/32000 : ℚ) (4713/5120 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_382 : Certificate start0_face1_leaf
    (planeBox (142961/128000 : ℚ) (36133/32000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_one (142961/128000 : ℚ) (36133/32000 : ℚ) (58127/64000 : ℚ) (4713/5120 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_380 start0_face1_node_381

theorem start0_face1_node_383 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (36133/32000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_zero (14139/12800 : ℚ) (142961/128000 : ℚ) (36133/32000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_379 start0_face1_node_382

theorem start0_face1_node_384 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (36133/32000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_one (14139/12800 : ℚ) (36133/32000 : ℚ) (14139/16000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_378 start0_face1_node_383

theorem start0_face1_node_385 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (14139/12800 : ℚ) (36133/32000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_377 start0_face1_node_384

theorem start0_face1_node_386 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (139819/128000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_387 : Certificate start0_face1_leaf
    (planeBox (139819/128000 : ℚ) (14139/12800 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_388 : Certificate start0_face1_leaf
    (planeBox (139819/128000 : ℚ) (14139/12800 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_389 : Certificate start0_face1_leaf
    (planeBox (139819/128000 : ℚ) (14139/12800 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ)) := by
  exact planeBox_split_one (139819/128000 : ℚ) (14139/12800 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_387 start0_face1_node_388

theorem start0_face1_node_390 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (14139/12800 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (139819/128000 : ℚ) (14139/12800 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_386 start0_face1_node_389

theorem start0_face1_node_391 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (139819/128000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

#print axioms start0_face1_node_391
end N11Formalization.SharedMomentConcreteFace1
