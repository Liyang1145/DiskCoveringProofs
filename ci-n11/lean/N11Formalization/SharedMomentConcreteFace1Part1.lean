import N11Formalization.SharedMomentConcreteFace1Part0

set_option autoImplicit false
noncomputable section
namespace N11Formalization.SharedMomentConcreteFace1
open RationalBoxSubdivision SharedMomentFacePlaneGradientCertificate SharedMomentFacePlaneCertificate
open SharedMomentFacePlaneDirectCertificate SharedMomentFactorRationalNodes
open SharedMomentFactorIntervalCertificate SharedMomentFactorLocalGradientCertificate
open RationalTrigLocalLipschitz

theorem start0_face1_node_392 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (139819/128000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_393 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (139819/128000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (139819/128000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_391 start0_face1_node_392

theorem start0_face1_node_394 : Certificate start0_face1_leaf
    (planeBox (139819/128000 : ℚ) (14139/12800 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_395 : Certificate start0_face1_leaf
    (planeBox (139819/128000 : ℚ) (14139/12800 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_396 : Certificate start0_face1_leaf
    (planeBox (139819/128000 : ℚ) (14139/12800 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (139819/128000 : ℚ) (14139/12800 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_394 start0_face1_node_395

theorem start0_face1_node_397 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (14139/12800 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (139819/128000 : ℚ) (14139/12800 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_393 start0_face1_node_396

theorem start0_face1_node_398 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (14139/12800 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (14139/12800 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_390 start0_face1_node_397

theorem start0_face1_node_399 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (142961/128000 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_400 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (284351/256000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_401 : Certificate start0_face1_leaf
    (planeBox (284351/256000 : ℚ) (142961/128000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_402 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (142961/128000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ)) := by
  exact planeBox_split_zero (14139/12800 : ℚ) (284351/256000 : ℚ) (142961/128000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_400 start0_face1_node_401

theorem start0_face1_node_403 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (142961/128000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ)) := by
  exact planeBox_split_one (14139/12800 : ℚ) (142961/128000 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_399 start0_face1_node_402

theorem start0_face1_node_404 : Certificate start0_face1_leaf
    (planeBox (142961/128000 : ℚ) (287493/256000 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_405 : Certificate start0_face1_leaf
    (planeBox (287493/256000 : ℚ) (36133/32000 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_406 : Certificate start0_face1_leaf
    (planeBox (142961/128000 : ℚ) (36133/32000 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ)) := by
  exact planeBox_split_zero (142961/128000 : ℚ) (287493/256000 : ℚ) (36133/32000 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_404 start0_face1_node_405

theorem start0_face1_node_407 : Certificate start0_face1_leaf
    (planeBox (142961/128000 : ℚ) (287493/256000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_408 : Certificate start0_face1_leaf
    (planeBox (287493/256000 : ℚ) (36133/32000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_409 : Certificate start0_face1_leaf
    (planeBox (142961/128000 : ℚ) (36133/32000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ)) := by
  exact planeBox_split_zero (142961/128000 : ℚ) (287493/256000 : ℚ) (36133/32000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_407 start0_face1_node_408

theorem start0_face1_node_410 : Certificate start0_face1_leaf
    (planeBox (142961/128000 : ℚ) (36133/32000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ)) := by
  exact planeBox_split_one (142961/128000 : ℚ) (36133/32000 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_406 start0_face1_node_409

theorem start0_face1_node_411 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (36133/32000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ)) := by
  exact planeBox_split_zero (14139/12800 : ℚ) (142961/128000 : ℚ) (36133/32000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_403 start0_face1_node_410

theorem start0_face1_node_412 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (284351/256000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_413 : Certificate start0_face1_leaf
    (planeBox (284351/256000 : ℚ) (142961/128000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_414 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (142961/128000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ)) := by
  exact planeBox_split_zero (14139/12800 : ℚ) (284351/256000 : ℚ) (142961/128000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_412 start0_face1_node_413

theorem start0_face1_node_415 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (284351/256000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_416 : Certificate start0_face1_leaf
    (planeBox (284351/256000 : ℚ) (142961/128000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_417 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (142961/128000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (14139/12800 : ℚ) (284351/256000 : ℚ) (142961/128000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_415 start0_face1_node_416

theorem start0_face1_node_418 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (142961/128000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (14139/12800 : ℚ) (142961/128000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_414 start0_face1_node_417

theorem start0_face1_node_419 : Certificate start0_face1_leaf
    (planeBox (142961/128000 : ℚ) (287493/256000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_420 : Certificate start0_face1_leaf
    (planeBox (287493/256000 : ℚ) (36133/32000 : ℚ) (61269/64000 : ℚ) (246647/256000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_421 : Certificate start0_face1_leaf
    (planeBox (287493/256000 : ℚ) (36133/32000 : ℚ) (246647/256000 : ℚ) (124109/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_422 : Certificate start0_face1_leaf
    (planeBox (287493/256000 : ℚ) (36133/32000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ)) := by
  exact planeBox_split_one (287493/256000 : ℚ) (36133/32000 : ℚ) (61269/64000 : ℚ) (246647/256000 : ℚ) (124109/128000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_420 start0_face1_node_421

theorem start0_face1_node_423 : Certificate start0_face1_leaf
    (planeBox (142961/128000 : ℚ) (36133/32000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ)) := by
  exact planeBox_split_zero (142961/128000 : ℚ) (287493/256000 : ℚ) (36133/32000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_419 start0_face1_node_422

theorem start0_face1_node_424 : Certificate start0_face1_leaf
    (planeBox (142961/128000 : ℚ) (287493/256000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_425 : Certificate start0_face1_leaf
    (planeBox (287493/256000 : ℚ) (36133/32000 : ℚ) (124109/128000 : ℚ) (249789/256000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_426 : Certificate start0_face1_leaf
    (planeBox (287493/256000 : ℚ) (36133/32000 : ℚ) (249789/256000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_427 : Certificate start0_face1_leaf
    (planeBox (287493/256000 : ℚ) (36133/32000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (287493/256000 : ℚ) (36133/32000 : ℚ) (124109/128000 : ℚ) (249789/256000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_425 start0_face1_node_426

theorem start0_face1_node_428 : Certificate start0_face1_leaf
    (planeBox (142961/128000 : ℚ) (36133/32000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (142961/128000 : ℚ) (287493/256000 : ℚ) (36133/32000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_424 start0_face1_node_427

theorem start0_face1_node_429 : Certificate start0_face1_leaf
    (planeBox (142961/128000 : ℚ) (36133/32000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (142961/128000 : ℚ) (36133/32000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_423 start0_face1_node_428

theorem start0_face1_node_430 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (36133/32000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (14139/12800 : ℚ) (142961/128000 : ℚ) (36133/32000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_418 start0_face1_node_429

theorem start0_face1_node_431 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (36133/32000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (14139/12800 : ℚ) (36133/32000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_411 start0_face1_node_430

theorem start0_face1_node_432 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (14139/12800 : ℚ) (36133/32000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_398 start0_face1_node_431

theorem start0_face1_node_433 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (36133/32000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_385 start0_face1_node_432

theorem start0_face1_node_434 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (146103/128000 : ℚ) (14139/16000 : ℚ) (58127/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_435 : Certificate start0_face1_leaf
    (planeBox (146103/128000 : ℚ) (73837/64000 : ℚ) (14139/16000 : ℚ) (58127/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_436 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (73837/64000 : ℚ) (14139/16000 : ℚ) (58127/64000 : ℚ)) := by
  exact planeBox_split_zero (36133/32000 : ℚ) (146103/128000 : ℚ) (73837/64000 : ℚ) (14139/16000 : ℚ) (58127/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_434 start0_face1_node_435

theorem start0_face1_node_437 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (146103/128000 : ℚ) (58127/64000 : ℚ) (4713/5120 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_438 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (146103/128000 : ℚ) (4713/5120 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_439 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (146103/128000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_one (36133/32000 : ℚ) (146103/128000 : ℚ) (58127/64000 : ℚ) (4713/5120 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_437 start0_face1_node_438

theorem start0_face1_node_440 : Certificate start0_face1_leaf
    (planeBox (146103/128000 : ℚ) (73837/64000 : ℚ) (58127/64000 : ℚ) (4713/5120 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_441 : Certificate start0_face1_leaf
    (planeBox (146103/128000 : ℚ) (73837/64000 : ℚ) (4713/5120 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_442 : Certificate start0_face1_leaf
    (planeBox (146103/128000 : ℚ) (73837/64000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_one (146103/128000 : ℚ) (73837/64000 : ℚ) (58127/64000 : ℚ) (4713/5120 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_440 start0_face1_node_441

theorem start0_face1_node_443 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (73837/64000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_zero (36133/32000 : ℚ) (146103/128000 : ℚ) (73837/64000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_439 start0_face1_node_442

theorem start0_face1_node_444 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (73837/64000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_one (36133/32000 : ℚ) (73837/64000 : ℚ) (14139/16000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_436 start0_face1_node_443

theorem start0_face1_node_445 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (29849/25600 : ℚ) (14139/16000 : ℚ) (58127/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_446 : Certificate start0_face1_leaf
    (planeBox (29849/25600 : ℚ) (4713/4000 : ℚ) (14139/16000 : ℚ) (58127/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_447 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (4713/4000 : ℚ) (14139/16000 : ℚ) (58127/64000 : ℚ)) := by
  exact planeBox_split_zero (73837/64000 : ℚ) (29849/25600 : ℚ) (4713/4000 : ℚ) (14139/16000 : ℚ) (58127/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_445 start0_face1_node_446

theorem start0_face1_node_448 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (29849/25600 : ℚ) (58127/64000 : ℚ) (4713/5120 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_449 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (29849/25600 : ℚ) (4713/5120 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_450 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (29849/25600 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_one (73837/64000 : ℚ) (29849/25600 : ℚ) (58127/64000 : ℚ) (4713/5120 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_448 start0_face1_node_449

theorem start0_face1_node_451 : Certificate start0_face1_leaf
    (planeBox (29849/25600 : ℚ) (4713/4000 : ℚ) (58127/64000 : ℚ) (4713/5120 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_452 : Certificate start0_face1_leaf
    (planeBox (29849/25600 : ℚ) (4713/4000 : ℚ) (4713/5120 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_453 : Certificate start0_face1_leaf
    (planeBox (29849/25600 : ℚ) (4713/4000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_one (29849/25600 : ℚ) (4713/4000 : ℚ) (58127/64000 : ℚ) (4713/5120 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_451 start0_face1_node_452

theorem start0_face1_node_454 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (4713/4000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_zero (73837/64000 : ℚ) (29849/25600 : ℚ) (4713/4000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_450 start0_face1_node_453

theorem start0_face1_node_455 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (4713/4000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_one (73837/64000 : ℚ) (4713/4000 : ℚ) (14139/16000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_447 start0_face1_node_454

theorem start0_face1_node_456 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_zero (36133/32000 : ℚ) (73837/64000 : ℚ) (4713/4000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_444 start0_face1_node_455

theorem start0_face1_node_457 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (58127/51200 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_458 : Certificate start0_face1_leaf
    (planeBox (58127/51200 : ℚ) (146103/128000 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_459 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (146103/128000 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ)) := by
  exact planeBox_split_zero (36133/32000 : ℚ) (58127/51200 : ℚ) (146103/128000 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_457 start0_face1_node_458

theorem start0_face1_node_460 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (58127/51200 : ℚ) (120967/128000 : ℚ) (48701/51200 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_461 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (58127/51200 : ℚ) (48701/51200 : ℚ) (61269/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_462 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (58127/51200 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ)) := by
  exact planeBox_split_one (36133/32000 : ℚ) (58127/51200 : ℚ) (120967/128000 : ℚ) (48701/51200 : ℚ) (61269/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_460 start0_face1_node_461

theorem start0_face1_node_463 : Certificate start0_face1_leaf
    (planeBox (58127/51200 : ℚ) (146103/128000 : ℚ) (120967/128000 : ℚ) (48701/51200 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_464 : Certificate start0_face1_leaf
    (planeBox (58127/51200 : ℚ) (146103/128000 : ℚ) (48701/51200 : ℚ) (61269/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_465 : Certificate start0_face1_leaf
    (planeBox (58127/51200 : ℚ) (146103/128000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ)) := by
  exact planeBox_split_one (58127/51200 : ℚ) (146103/128000 : ℚ) (120967/128000 : ℚ) (48701/51200 : ℚ) (61269/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_463 start0_face1_node_464

theorem start0_face1_node_466 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (146103/128000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ)) := by
  exact planeBox_split_zero (36133/32000 : ℚ) (58127/51200 : ℚ) (146103/128000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_462 start0_face1_node_465

theorem start0_face1_node_467 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (146103/128000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ)) := by
  exact planeBox_split_one (36133/32000 : ℚ) (146103/128000 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_459 start0_face1_node_466

theorem start0_face1_node_468 : Certificate start0_face1_leaf
    (planeBox (146103/128000 : ℚ) (293777/256000 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_469 : Certificate start0_face1_leaf
    (planeBox (293777/256000 : ℚ) (73837/64000 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_470 : Certificate start0_face1_leaf
    (planeBox (146103/128000 : ℚ) (73837/64000 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ)) := by
  exact planeBox_split_zero (146103/128000 : ℚ) (293777/256000 : ℚ) (73837/64000 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_468 start0_face1_node_469

theorem start0_face1_node_471 : Certificate start0_face1_leaf
    (planeBox (146103/128000 : ℚ) (293777/256000 : ℚ) (120967/128000 : ℚ) (48701/51200 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_472 : Certificate start0_face1_leaf
    (planeBox (146103/128000 : ℚ) (293777/256000 : ℚ) (48701/51200 : ℚ) (61269/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_473 : Certificate start0_face1_leaf
    (planeBox (146103/128000 : ℚ) (293777/256000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ)) := by
  exact planeBox_split_one (146103/128000 : ℚ) (293777/256000 : ℚ) (120967/128000 : ℚ) (48701/51200 : ℚ) (61269/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_471 start0_face1_node_472

theorem start0_face1_node_474 : Certificate start0_face1_leaf
    (planeBox (293777/256000 : ℚ) (73837/64000 : ℚ) (120967/128000 : ℚ) (48701/51200 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_475 : Certificate start0_face1_leaf
    (planeBox (293777/256000 : ℚ) (73837/64000 : ℚ) (48701/51200 : ℚ) (61269/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_476 : Certificate start0_face1_leaf
    (planeBox (293777/256000 : ℚ) (73837/64000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ)) := by
  exact planeBox_split_one (293777/256000 : ℚ) (73837/64000 : ℚ) (120967/128000 : ℚ) (48701/51200 : ℚ) (61269/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_474 start0_face1_node_475

theorem start0_face1_node_477 : Certificate start0_face1_leaf
    (planeBox (146103/128000 : ℚ) (73837/64000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ)) := by
  exact planeBox_split_zero (146103/128000 : ℚ) (293777/256000 : ℚ) (73837/64000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_473 start0_face1_node_476

theorem start0_face1_node_478 : Certificate start0_face1_leaf
    (planeBox (146103/128000 : ℚ) (73837/64000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ)) := by
  exact planeBox_split_one (146103/128000 : ℚ) (73837/64000 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_470 start0_face1_node_477

theorem start0_face1_node_479 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (73837/64000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ)) := by
  exact planeBox_split_zero (36133/32000 : ℚ) (146103/128000 : ℚ) (73837/64000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_467 start0_face1_node_478

theorem start0_face1_node_480 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (58127/51200 : ℚ) (61269/64000 : ℚ) (246647/256000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_481 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (58127/51200 : ℚ) (246647/256000 : ℚ) (124109/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_482 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (58127/51200 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ)) := by
  exact planeBox_split_one (36133/32000 : ℚ) (58127/51200 : ℚ) (61269/64000 : ℚ) (246647/256000 : ℚ) (124109/128000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_480 start0_face1_node_481

theorem start0_face1_node_483 : Certificate start0_face1_leaf
    (planeBox (58127/51200 : ℚ) (146103/128000 : ℚ) (61269/64000 : ℚ) (246647/256000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_484 : Certificate start0_face1_leaf
    (planeBox (58127/51200 : ℚ) (146103/128000 : ℚ) (246647/256000 : ℚ) (124109/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_485 : Certificate start0_face1_leaf
    (planeBox (58127/51200 : ℚ) (146103/128000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ)) := by
  exact planeBox_split_one (58127/51200 : ℚ) (146103/128000 : ℚ) (61269/64000 : ℚ) (246647/256000 : ℚ) (124109/128000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_483 start0_face1_node_484

theorem start0_face1_node_486 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (146103/128000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ)) := by
  exact planeBox_split_zero (36133/32000 : ℚ) (58127/51200 : ℚ) (146103/128000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_482 start0_face1_node_485

theorem start0_face1_node_487 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (58127/51200 : ℚ) (124109/128000 : ℚ) (249789/256000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_488 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (58127/51200 : ℚ) (249789/256000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_489 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (58127/51200 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (36133/32000 : ℚ) (58127/51200 : ℚ) (124109/128000 : ℚ) (249789/256000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_487 start0_face1_node_488

theorem start0_face1_node_490 : Certificate start0_face1_leaf
    (planeBox (58127/51200 : ℚ) (146103/128000 : ℚ) (124109/128000 : ℚ) (249789/256000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_491 : Certificate start0_face1_leaf
    (planeBox (58127/51200 : ℚ) (146103/128000 : ℚ) (249789/256000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_492 : Certificate start0_face1_leaf
    (planeBox (58127/51200 : ℚ) (146103/128000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (58127/51200 : ℚ) (146103/128000 : ℚ) (124109/128000 : ℚ) (249789/256000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_490 start0_face1_node_491

theorem start0_face1_node_493 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (146103/128000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (36133/32000 : ℚ) (58127/51200 : ℚ) (146103/128000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_489 start0_face1_node_492

theorem start0_face1_node_494 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (146103/128000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (36133/32000 : ℚ) (146103/128000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_486 start0_face1_node_493

theorem start0_face1_node_495 : Certificate start0_face1_leaf
    (planeBox (146103/128000 : ℚ) (293777/256000 : ℚ) (61269/64000 : ℚ) (246647/256000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_496 : Certificate start0_face1_leaf
    (planeBox (146103/128000 : ℚ) (293777/256000 : ℚ) (246647/256000 : ℚ) (124109/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_497 : Certificate start0_face1_leaf
    (planeBox (146103/128000 : ℚ) (293777/256000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ)) := by
  exact planeBox_split_one (146103/128000 : ℚ) (293777/256000 : ℚ) (61269/64000 : ℚ) (246647/256000 : ℚ) (124109/128000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_495 start0_face1_node_496

theorem start0_face1_node_498 : Certificate start0_face1_leaf
    (planeBox (293777/256000 : ℚ) (73837/64000 : ℚ) (61269/64000 : ℚ) (246647/256000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_499 : Certificate start0_face1_leaf
    (planeBox (293777/256000 : ℚ) (73837/64000 : ℚ) (246647/256000 : ℚ) (124109/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_500 : Certificate start0_face1_leaf
    (planeBox (293777/256000 : ℚ) (73837/64000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ)) := by
  exact planeBox_split_one (293777/256000 : ℚ) (73837/64000 : ℚ) (61269/64000 : ℚ) (246647/256000 : ℚ) (124109/128000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_498 start0_face1_node_499

theorem start0_face1_node_501 : Certificate start0_face1_leaf
    (planeBox (146103/128000 : ℚ) (73837/64000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ)) := by
  exact planeBox_split_zero (146103/128000 : ℚ) (293777/256000 : ℚ) (73837/64000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_497 start0_face1_node_500

theorem start0_face1_node_502 : Certificate start0_face1_leaf
    (planeBox (146103/128000 : ℚ) (293777/256000 : ℚ) (124109/128000 : ℚ) (249789/256000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_503 : Certificate start0_face1_leaf
    (planeBox (146103/128000 : ℚ) (293777/256000 : ℚ) (249789/256000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_504 : Certificate start0_face1_leaf
    (planeBox (146103/128000 : ℚ) (293777/256000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (146103/128000 : ℚ) (293777/256000 : ℚ) (124109/128000 : ℚ) (249789/256000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_502 start0_face1_node_503

theorem start0_face1_node_505 : Certificate start0_face1_leaf
    (planeBox (293777/256000 : ℚ) (73837/64000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_506 : Certificate start0_face1_leaf
    (planeBox (146103/128000 : ℚ) (73837/64000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (146103/128000 : ℚ) (293777/256000 : ℚ) (73837/64000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_504 start0_face1_node_505

theorem start0_face1_node_507 : Certificate start0_face1_leaf
    (planeBox (146103/128000 : ℚ) (73837/64000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (146103/128000 : ℚ) (73837/64000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_501 start0_face1_node_506

theorem start0_face1_node_508 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (73837/64000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (36133/32000 : ℚ) (146103/128000 : ℚ) (73837/64000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_494 start0_face1_node_507

theorem start0_face1_node_509 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (73837/64000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (36133/32000 : ℚ) (73837/64000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_479 start0_face1_node_508

theorem start0_face1_node_510 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (296919/256000 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_511 : Certificate start0_face1_leaf
    (planeBox (296919/256000 : ℚ) (29849/25600 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_512 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (29849/25600 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ)) := by
  exact planeBox_split_zero (73837/64000 : ℚ) (296919/256000 : ℚ) (29849/25600 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_510 start0_face1_node_511

theorem start0_face1_node_513 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (296919/256000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_514 : Certificate start0_face1_leaf
    (planeBox (296919/256000 : ℚ) (29849/25600 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_515 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (29849/25600 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ)) := by
  exact planeBox_split_zero (73837/64000 : ℚ) (296919/256000 : ℚ) (29849/25600 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_513 start0_face1_node_514

theorem start0_face1_node_516 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (29849/25600 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ)) := by
  exact planeBox_split_one (73837/64000 : ℚ) (29849/25600 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_512 start0_face1_node_515

theorem start0_face1_node_517 : Certificate start0_face1_leaf
    (planeBox (29849/25600 : ℚ) (4713/4000 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_518 : Certificate start0_face1_leaf
    (planeBox (29849/25600 : ℚ) (300061/256000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_519 : Certificate start0_face1_leaf
    (planeBox (300061/256000 : ℚ) (4713/4000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_520 : Certificate start0_face1_leaf
    (planeBox (29849/25600 : ℚ) (4713/4000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ)) := by
  exact planeBox_split_zero (29849/25600 : ℚ) (300061/256000 : ℚ) (4713/4000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_518 start0_face1_node_519

theorem start0_face1_node_521 : Certificate start0_face1_leaf
    (planeBox (29849/25600 : ℚ) (4713/4000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ)) := by
  exact planeBox_split_one (29849/25600 : ℚ) (4713/4000 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_517 start0_face1_node_520

theorem start0_face1_node_522 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (4713/4000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ)) := by
  exact planeBox_split_zero (73837/64000 : ℚ) (29849/25600 : ℚ) (4713/4000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_516 start0_face1_node_521

theorem start0_face1_node_523 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (296919/256000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_524 : Certificate start0_face1_leaf
    (planeBox (296919/256000 : ℚ) (29849/25600 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_525 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (29849/25600 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ)) := by
  exact planeBox_split_zero (73837/64000 : ℚ) (296919/256000 : ℚ) (29849/25600 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_523 start0_face1_node_524

theorem start0_face1_node_526 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (296919/256000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_527 : Certificate start0_face1_leaf
    (planeBox (296919/256000 : ℚ) (29849/25600 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_528 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (29849/25600 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (73837/64000 : ℚ) (296919/256000 : ℚ) (29849/25600 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_526 start0_face1_node_527

theorem start0_face1_node_529 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (29849/25600 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (73837/64000 : ℚ) (29849/25600 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_525 start0_face1_node_528

theorem start0_face1_node_530 : Certificate start0_face1_leaf
    (planeBox (29849/25600 : ℚ) (300061/256000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_531 : Certificate start0_face1_leaf
    (planeBox (300061/256000 : ℚ) (4713/4000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_532 : Certificate start0_face1_leaf
    (planeBox (29849/25600 : ℚ) (4713/4000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ)) := by
  exact planeBox_split_zero (29849/25600 : ℚ) (300061/256000 : ℚ) (4713/4000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_530 start0_face1_node_531

theorem start0_face1_node_533 : Certificate start0_face1_leaf
    (planeBox (29849/25600 : ℚ) (4713/4000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_534 : Certificate start0_face1_leaf
    (planeBox (29849/25600 : ℚ) (4713/4000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (29849/25600 : ℚ) (4713/4000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_532 start0_face1_node_533

theorem start0_face1_node_535 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (4713/4000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (73837/64000 : ℚ) (29849/25600 : ℚ) (4713/4000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_529 start0_face1_node_534

theorem start0_face1_node_536 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (4713/4000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (73837/64000 : ℚ) (4713/4000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_522 start0_face1_node_535

theorem start0_face1_node_537 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (36133/32000 : ℚ) (73837/64000 : ℚ) (4713/4000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_509 start0_face1_node_536

theorem start0_face1_node_538 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (36133/32000 : ℚ) (4713/4000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_456 start0_face1_node_537

theorem start0_face1_node_539 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_433 start0_face1_node_538

theorem start0_face1_node_540 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_372 start0_face1_node_539

theorem start0_face1_node_541 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_353 start0_face1_node_540

theorem start0_face1_node_542 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (64411/64000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_543 : Certificate start0_face1_leaf
    (planeBox (64411/64000 : ℚ) (32991/32000 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_544 : Certificate start0_face1_leaf
    (planeBox (64411/64000 : ℚ) (32991/32000 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_545 : Certificate start0_face1_leaf
    (planeBox (64411/64000 : ℚ) (32991/32000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ)) := by
  exact planeBox_split_one (64411/64000 : ℚ) (32991/32000 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_543 start0_face1_node_544

theorem start0_face1_node_546 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_542 start0_face1_node_545

theorem start0_face1_node_547 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_548 : Certificate start0_face1_leaf
    (planeBox (64411/64000 : ℚ) (32991/32000 : ℚ) (32991/32000 : ℚ) (67553/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_549 : Certificate start0_face1_leaf
    (planeBox (64411/64000 : ℚ) (32991/32000 : ℚ) (67553/64000 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_550 : Certificate start0_face1_leaf
    (planeBox (64411/64000 : ℚ) (32991/32000 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_one (64411/64000 : ℚ) (32991/32000 : ℚ) (32991/32000 : ℚ) (67553/64000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_548 start0_face1_node_549

theorem start0_face1_node_551 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_547 start0_face1_node_550

theorem start0_face1_node_552 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (32991/32000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_546 start0_face1_node_551

theorem start0_face1_node_553 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (67553/64000 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_554 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (67553/64000 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_555 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (67553/64000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ)) := by
  exact planeBox_split_one (32991/32000 : ℚ) (67553/64000 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_553 start0_face1_node_554

theorem start0_face1_node_556 : Certificate start0_face1_leaf
    (planeBox (67553/64000 : ℚ) (136677/128000 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_557 : Certificate start0_face1_leaf
    (planeBox (136677/128000 : ℚ) (17281/16000 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_558 : Certificate start0_face1_leaf
    (planeBox (67553/64000 : ℚ) (17281/16000 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ)) := by
  exact planeBox_split_zero (67553/64000 : ℚ) (136677/128000 : ℚ) (17281/16000 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_556 start0_face1_node_557

theorem start0_face1_node_559 : Certificate start0_face1_leaf
    (planeBox (67553/64000 : ℚ) (136677/128000 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_560 : Certificate start0_face1_leaf
    (planeBox (136677/128000 : ℚ) (17281/16000 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_561 : Certificate start0_face1_leaf
    (planeBox (67553/64000 : ℚ) (17281/16000 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ)) := by
  exact planeBox_split_zero (67553/64000 : ℚ) (136677/128000 : ℚ) (17281/16000 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_559 start0_face1_node_560

theorem start0_face1_node_562 : Certificate start0_face1_leaf
    (planeBox (67553/64000 : ℚ) (17281/16000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ)) := by
  exact planeBox_split_one (67553/64000 : ℚ) (17281/16000 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_558 start0_face1_node_561

theorem start0_face1_node_563 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ)) := by
  exact planeBox_split_zero (32991/32000 : ℚ) (67553/64000 : ℚ) (17281/16000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_555 start0_face1_node_562

theorem start0_face1_node_564 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (67553/64000 : ℚ) (32991/32000 : ℚ) (67553/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_565 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (67553/64000 : ℚ) (67553/64000 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_566 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (67553/64000 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_one (32991/32000 : ℚ) (67553/64000 : ℚ) (32991/32000 : ℚ) (67553/64000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_564 start0_face1_node_565

theorem start0_face1_node_567 : Certificate start0_face1_leaf
    (planeBox (67553/64000 : ℚ) (17281/16000 : ℚ) (32991/32000 : ℚ) (67553/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_568 : Certificate start0_face1_leaf
    (planeBox (67553/64000 : ℚ) (17281/16000 : ℚ) (67553/64000 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_569 : Certificate start0_face1_leaf
    (planeBox (67553/64000 : ℚ) (17281/16000 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_one (67553/64000 : ℚ) (17281/16000 : ℚ) (32991/32000 : ℚ) (67553/64000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_567 start0_face1_node_568

theorem start0_face1_node_570 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_zero (32991/32000 : ℚ) (67553/64000 : ℚ) (17281/16000 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_566 start0_face1_node_569

theorem start0_face1_node_571 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_one (32991/32000 : ℚ) (17281/16000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_563 start0_face1_node_570

theorem start0_face1_node_572 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_552 start0_face1_node_571

theorem start0_face1_node_573 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (64411/64000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_574 : Certificate start0_face1_leaf
    (planeBox (64411/64000 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_575 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_573 start0_face1_node_574

theorem start0_face1_node_576 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_577 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_575 start0_face1_node_576

theorem start0_face1_node_578 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (67553/64000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_579 : Certificate start0_face1_leaf
    (planeBox (67553/64000 : ℚ) (17281/16000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_580 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ)) := by
  exact planeBox_split_zero (32991/32000 : ℚ) (67553/64000 : ℚ) (17281/16000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_578 start0_face1_node_579

theorem start0_face1_node_581 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_582 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (32991/32000 : ℚ) (17281/16000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_580 start0_face1_node_581

theorem start0_face1_node_583 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_577 start0_face1_node_582

theorem start0_face1_node_584 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (17281/16000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_572 start0_face1_node_583

theorem start0_face1_node_585 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (139819/128000 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_586 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (139819/128000 : ℚ) (127251/128000 : ℚ) (64411/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_587 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (139819/128000 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (139819/128000 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ) (64411/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_585 start0_face1_node_586

theorem start0_face1_node_588 : Certificate start0_face1_leaf
    (planeBox (139819/128000 : ℚ) (14139/12800 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_589 : Certificate start0_face1_leaf
    (planeBox (139819/128000 : ℚ) (14139/12800 : ℚ) (127251/128000 : ℚ) (64411/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_590 : Certificate start0_face1_leaf
    (planeBox (139819/128000 : ℚ) (14139/12800 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ)) := by
  exact planeBox_split_one (139819/128000 : ℚ) (14139/12800 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ) (64411/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_588 start0_face1_node_589

theorem start0_face1_node_591 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (14139/12800 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (139819/128000 : ℚ) (14139/12800 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_587 start0_face1_node_590

theorem start0_face1_node_592 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (139819/128000 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_593 : Certificate start0_face1_leaf
    (planeBox (139819/128000 : ℚ) (14139/12800 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_594 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (14139/12800 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (139819/128000 : ℚ) (14139/12800 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_592 start0_face1_node_593

theorem start0_face1_node_595 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (14139/12800 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (14139/12800 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_591 start0_face1_node_594

theorem start0_face1_node_596 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (284351/256000 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_597 : Certificate start0_face1_leaf
    (planeBox (284351/256000 : ℚ) (142961/128000 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_598 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (142961/128000 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ)) := by
  exact planeBox_split_zero (14139/12800 : ℚ) (284351/256000 : ℚ) (142961/128000 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_596 start0_face1_node_597

theorem start0_face1_node_599 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (142961/128000 : ℚ) (127251/128000 : ℚ) (64411/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_600 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (142961/128000 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ)) := by
  exact planeBox_split_one (14139/12800 : ℚ) (142961/128000 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ) (64411/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_598 start0_face1_node_599

theorem start0_face1_node_601 : Certificate start0_face1_leaf
    (planeBox (142961/128000 : ℚ) (287493/256000 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_602 : Certificate start0_face1_leaf
    (planeBox (287493/256000 : ℚ) (36133/32000 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_603 : Certificate start0_face1_leaf
    (planeBox (142961/128000 : ℚ) (36133/32000 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ)) := by
  exact planeBox_split_zero (142961/128000 : ℚ) (287493/256000 : ℚ) (36133/32000 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_601 start0_face1_node_602

theorem start0_face1_node_604 : Certificate start0_face1_leaf
    (planeBox (142961/128000 : ℚ) (36133/32000 : ℚ) (127251/128000 : ℚ) (64411/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_605 : Certificate start0_face1_leaf
    (planeBox (142961/128000 : ℚ) (36133/32000 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ)) := by
  exact planeBox_split_one (142961/128000 : ℚ) (36133/32000 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ) (64411/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_603 start0_face1_node_604

theorem start0_face1_node_606 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (36133/32000 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ)) := by
  exact planeBox_split_zero (14139/12800 : ℚ) (142961/128000 : ℚ) (36133/32000 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_600 start0_face1_node_605

theorem start0_face1_node_607 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (142961/128000 : ℚ) (64411/64000 : ℚ) (130393/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_608 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (142961/128000 : ℚ) (130393/128000 : ℚ) (32991/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_609 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (142961/128000 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ)) := by
  exact planeBox_split_one (14139/12800 : ℚ) (142961/128000 : ℚ) (64411/64000 : ℚ) (130393/128000 : ℚ) (32991/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_607 start0_face1_node_608

theorem start0_face1_node_610 : Certificate start0_face1_leaf
    (planeBox (142961/128000 : ℚ) (36133/32000 : ℚ) (64411/64000 : ℚ) (130393/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_611 : Certificate start0_face1_leaf
    (planeBox (142961/128000 : ℚ) (36133/32000 : ℚ) (130393/128000 : ℚ) (32991/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_612 : Certificate start0_face1_leaf
    (planeBox (142961/128000 : ℚ) (36133/32000 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ)) := by
  exact planeBox_split_one (142961/128000 : ℚ) (36133/32000 : ℚ) (64411/64000 : ℚ) (130393/128000 : ℚ) (32991/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_610 start0_face1_node_611

theorem start0_face1_node_613 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (36133/32000 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ)) := by
  exact planeBox_split_zero (14139/12800 : ℚ) (142961/128000 : ℚ) (36133/32000 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_609 start0_face1_node_612

theorem start0_face1_node_614 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (36133/32000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ)) := by
  exact planeBox_split_one (14139/12800 : ℚ) (36133/32000 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_606 start0_face1_node_613

theorem start0_face1_node_615 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (14139/12800 : ℚ) (36133/32000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_595 start0_face1_node_614

theorem start0_face1_node_616 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (14139/12800 : ℚ) (32991/32000 : ℚ) (67553/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_617 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (14139/12800 : ℚ) (67553/64000 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_618 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (14139/12800 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (14139/12800 : ℚ) (32991/32000 : ℚ) (67553/64000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_616 start0_face1_node_617

theorem start0_face1_node_619 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (36133/32000 : ℚ) (32991/32000 : ℚ) (67553/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_620 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (36133/32000 : ℚ) (67553/64000 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_621 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (36133/32000 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_one (14139/12800 : ℚ) (36133/32000 : ℚ) (32991/32000 : ℚ) (67553/64000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_619 start0_face1_node_620

theorem start0_face1_node_622 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (14139/12800 : ℚ) (36133/32000 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_618 start0_face1_node_621

theorem start0_face1_node_623 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (36133/32000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_615 start0_face1_node_622

theorem start0_face1_node_624 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (58127/51200 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_625 : Certificate start0_face1_leaf
    (planeBox (58127/51200 : ℚ) (146103/128000 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_626 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (146103/128000 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ)) := by
  exact planeBox_split_zero (36133/32000 : ℚ) (58127/51200 : ℚ) (146103/128000 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_624 start0_face1_node_625

theorem start0_face1_node_627 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (146103/128000 : ℚ) (127251/128000 : ℚ) (64411/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_628 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (146103/128000 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ)) := by
  exact planeBox_split_one (36133/32000 : ℚ) (146103/128000 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ) (64411/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_626 start0_face1_node_627

theorem start0_face1_node_629 : Certificate start0_face1_leaf
    (planeBox (146103/128000 : ℚ) (293777/256000 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_630 : Certificate start0_face1_leaf
    (planeBox (293777/256000 : ℚ) (73837/64000 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_631 : Certificate start0_face1_leaf
    (planeBox (146103/128000 : ℚ) (73837/64000 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ)) := by
  exact planeBox_split_zero (146103/128000 : ℚ) (293777/256000 : ℚ) (73837/64000 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_629 start0_face1_node_630

theorem start0_face1_node_632 : Certificate start0_face1_leaf
    (planeBox (146103/128000 : ℚ) (73837/64000 : ℚ) (127251/128000 : ℚ) (64411/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_633 : Certificate start0_face1_leaf
    (planeBox (146103/128000 : ℚ) (73837/64000 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ)) := by
  exact planeBox_split_one (146103/128000 : ℚ) (73837/64000 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ) (64411/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_631 start0_face1_node_632

theorem start0_face1_node_634 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (73837/64000 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ)) := by
  exact planeBox_split_zero (36133/32000 : ℚ) (146103/128000 : ℚ) (73837/64000 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_628 start0_face1_node_633

theorem start0_face1_node_635 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (146103/128000 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_636 : Certificate start0_face1_leaf
    (planeBox (146103/128000 : ℚ) (73837/64000 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_637 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (73837/64000 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ)) := by
  exact planeBox_split_zero (36133/32000 : ℚ) (146103/128000 : ℚ) (73837/64000 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_635 start0_face1_node_636

theorem start0_face1_node_638 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (73837/64000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ)) := by
  exact planeBox_split_one (36133/32000 : ℚ) (73837/64000 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_634 start0_face1_node_637

theorem start0_face1_node_639 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (29849/25600 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_640 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (29849/25600 : ℚ) (127251/128000 : ℚ) (64411/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_641 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (29849/25600 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ)) := by
  exact planeBox_split_one (73837/64000 : ℚ) (29849/25600 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ) (64411/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_639 start0_face1_node_640

theorem start0_face1_node_642 : Certificate start0_face1_leaf
    (planeBox (29849/25600 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_643 : Certificate start0_face1_leaf
    (planeBox (29849/25600 : ℚ) (4713/4000 : ℚ) (127251/128000 : ℚ) (64411/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_644 : Certificate start0_face1_leaf
    (planeBox (29849/25600 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ)) := by
  exact planeBox_split_one (29849/25600 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (127251/128000 : ℚ) (64411/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_642 start0_face1_node_643

theorem start0_face1_node_645 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ)) := by
  exact planeBox_split_zero (73837/64000 : ℚ) (29849/25600 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_641 start0_face1_node_644

theorem start0_face1_node_646 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (29849/25600 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_647 : Certificate start0_face1_leaf
    (planeBox (29849/25600 : ℚ) (4713/4000 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_648 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (4713/4000 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ)) := by
  exact planeBox_split_zero (73837/64000 : ℚ) (29849/25600 : ℚ) (4713/4000 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_646 start0_face1_node_647

theorem start0_face1_node_649 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ)) := by
  exact planeBox_split_one (73837/64000 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_645 start0_face1_node_648

theorem start0_face1_node_650 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ)) := by
  exact planeBox_split_zero (36133/32000 : ℚ) (73837/64000 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_638 start0_face1_node_649

theorem start0_face1_node_651 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (73837/64000 : ℚ) (32991/32000 : ℚ) (67553/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_652 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (73837/64000 : ℚ) (67553/64000 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_653 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (73837/64000 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_one (36133/32000 : ℚ) (73837/64000 : ℚ) (32991/32000 : ℚ) (67553/64000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_651 start0_face1_node_652

theorem start0_face1_node_654 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (4713/4000 : ℚ) (32991/32000 : ℚ) (67553/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_655 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (4713/4000 : ℚ) (67553/64000 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_656 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (4713/4000 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_one (73837/64000 : ℚ) (4713/4000 : ℚ) (32991/32000 : ℚ) (67553/64000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_654 start0_face1_node_655

theorem start0_face1_node_657 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_zero (36133/32000 : ℚ) (73837/64000 : ℚ) (4713/4000 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_653 start0_face1_node_656

theorem start0_face1_node_658 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_one (36133/32000 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_650 start0_face1_node_657

theorem start0_face1_node_659 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_623 start0_face1_node_658

theorem start0_face1_node_660 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (14139/12800 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_661 : Certificate start0_face1_leaf
    (planeBox (14139/12800 : ℚ) (36133/32000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_662 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (14139/12800 : ℚ) (36133/32000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_660 start0_face1_node_661

theorem start0_face1_node_663 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_664 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (36133/32000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_662 start0_face1_node_663

theorem start0_face1_node_665 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (73837/64000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_666 : Certificate start0_face1_leaf
    (planeBox (73837/64000 : ℚ) (4713/4000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_667 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ)) := by
  exact planeBox_split_zero (36133/32000 : ℚ) (73837/64000 : ℚ) (4713/4000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_665 start0_face1_node_666

theorem start0_face1_node_668 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_669 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (36133/32000 : ℚ) (4713/4000 : ℚ) (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_667 start0_face1_node_668

theorem start0_face1_node_670 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_664 start0_face1_node_669

theorem start0_face1_node_671 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_659 start0_face1_node_670

theorem start0_face1_node_672 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_584 start0_face1_node_671

theorem start0_face1_node_673 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_541 start0_face1_node_672

theorem start0_face1_node_674 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_316 start0_face1_node_673

theorem start0_face1_node_675 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_676 : Certificate start0_face1_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_677 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_675 start0_face1_node_676

theorem start0_face1_node_678 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_679 : Certificate start0_face1_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_680 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_678 start0_face1_node_679

theorem start0_face1_node_681 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (14139/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_677 start0_face1_node_680

theorem start0_face1_node_682 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_683 : Certificate start0_face1_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_684 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_682 start0_face1_node_683

theorem start0_face1_node_685 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_686 : Certificate start0_face1_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_687 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_685 start0_face1_node_686

theorem start0_face1_node_688 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_684 start0_face1_node_687

theorem start0_face1_node_689 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_681 start0_face1_node_688

theorem start0_face1_node_690 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (26707/32000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_691 : Certificate start0_face1_leaf
    (planeBox (26707/32000 : ℚ) (14139/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_692 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_690 start0_face1_node_691

theorem start0_face1_node_693 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_694 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (14139/16000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (14139/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_692 start0_face1_node_693

theorem start0_face1_node_695 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (29849/32000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_696 : Certificate start0_face1_leaf
    (planeBox (29849/32000 : ℚ) (1571/1600 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_697 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  exact planeBox_split_zero (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_695 start0_face1_node_696

theorem start0_face1_node_698 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_699 : Certificate start0_face1_leaf
    (planeBox (14139/16000 : ℚ) (1571/1600 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (14139/16000 : ℚ) (1571/1600 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_697 start0_face1_node_698

theorem start0_face1_node_700 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_694 start0_face1_node_699

theorem start0_face1_node_701 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_689 start0_face1_node_700

theorem start0_face1_node_702 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_703 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_704 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_702 start0_face1_node_703

theorem start0_face1_node_705 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_706 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_707 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_705 start0_face1_node_706

theorem start0_face1_node_708 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_704 start0_face1_node_707

theorem start0_face1_node_709 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_710 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_711 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_709 start0_face1_node_710

theorem start0_face1_node_712 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_713 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_714 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_712 start0_face1_node_713

theorem start0_face1_node_715 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_711 start0_face1_node_714

theorem start0_face1_node_716 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_708 start0_face1_node_715

theorem start0_face1_node_717 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (32991/32000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_718 : Certificate start0_face1_leaf
    (planeBox (32991/32000 : ℚ) (17281/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_719 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_717 start0_face1_node_718

theorem start0_face1_node_720 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_721 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (17281/16000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (17281/16000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_719 start0_face1_node_720

theorem start0_face1_node_722 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (36133/32000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_723 : Certificate start0_face1_leaf
    (planeBox (36133/32000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_724 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ)) := by
  exact planeBox_split_zero (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_722 start0_face1_node_723

theorem start0_face1_node_725 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_726 : Certificate start0_face1_leaf
    (planeBox (17281/16000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (17281/16000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (4713/3200 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_724 start0_face1_node_725

theorem start0_face1_node_727 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_721 start0_face1_node_726

theorem start0_face1_node_728 : Certificate start0_face1_leaf
    (planeBox (1571/1600 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/1600 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_716 start0_face1_node_727

theorem start0_face1_node_729 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_zero (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_701 start0_face1_node_728

theorem start0_face1_node_730 : Certificate start0_face1_leaf
    (planeBox (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ)) := by
  exact planeBox_split_one (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_674 start0_face1_node_729

theorem start0_face1_node_731 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (76979/64000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_732 : Certificate start0_face1_leaf
    (planeBox (76979/64000 : ℚ) (1571/1280 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_733 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (1571/1280 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (76979/64000 : ℚ) (1571/1280 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_731 start0_face1_node_732

theorem start0_face1_node_734 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (76979/64000 : ℚ) (26707/32000 : ℚ) (10997/12800 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_735 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (76979/64000 : ℚ) (10997/12800 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_736 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (76979/64000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (76979/64000 : ℚ) (26707/32000 : ℚ) (10997/12800 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_734 start0_face1_node_735

theorem start0_face1_node_737 : Certificate start0_face1_leaf
    (planeBox (76979/64000 : ℚ) (1571/1280 : ℚ) (26707/32000 : ℚ) (10997/12800 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_738 : Certificate start0_face1_leaf
    (planeBox (76979/64000 : ℚ) (1571/1280 : ℚ) (10997/12800 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_739 : Certificate start0_face1_leaf
    (planeBox (76979/64000 : ℚ) (1571/1280 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_one (76979/64000 : ℚ) (1571/1280 : ℚ) (26707/32000 : ℚ) (10997/12800 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_737 start0_face1_node_738

theorem start0_face1_node_740 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (1571/1280 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (76979/64000 : ℚ) (1571/1280 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_736 start0_face1_node_739

theorem start0_face1_node_741 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (1571/1280 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (1571/1280 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_733 start0_face1_node_740

theorem start0_face1_node_742 : Certificate start0_face1_leaf
    (planeBox (1571/1280 : ℚ) (80121/64000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_743 : Certificate start0_face1_leaf
    (planeBox (80121/64000 : ℚ) (20423/16000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_744 : Certificate start0_face1_leaf
    (planeBox (1571/1280 : ℚ) (20423/16000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ)) := by
  exact planeBox_split_zero (1571/1280 : ℚ) (80121/64000 : ℚ) (20423/16000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_742 start0_face1_node_743

theorem start0_face1_node_745 : Certificate start0_face1_leaf
    (planeBox (1571/1280 : ℚ) (80121/64000 : ℚ) (26707/32000 : ℚ) (10997/12800 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_746 : Certificate start0_face1_leaf
    (planeBox (1571/1280 : ℚ) (80121/64000 : ℚ) (10997/12800 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_747 : Certificate start0_face1_leaf
    (planeBox (1571/1280 : ℚ) (80121/64000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_one (1571/1280 : ℚ) (80121/64000 : ℚ) (26707/32000 : ℚ) (10997/12800 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_745 start0_face1_node_746

theorem start0_face1_node_748 : Certificate start0_face1_leaf
    (planeBox (80121/64000 : ℚ) (20423/16000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_749 : Certificate start0_face1_leaf
    (planeBox (1571/1280 : ℚ) (20423/16000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_zero (1571/1280 : ℚ) (80121/64000 : ℚ) (20423/16000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_747 start0_face1_node_748

theorem start0_face1_node_750 : Certificate start0_face1_leaf
    (planeBox (1571/1280 : ℚ) (20423/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_one (1571/1280 : ℚ) (20423/16000 : ℚ) (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_744 start0_face1_node_749

theorem start0_face1_node_751 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (20423/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (1571/1280 : ℚ) (20423/16000 : ℚ) (1571/2000 : ℚ) (14139/16000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_741 start0_face1_node_750

theorem start0_face1_node_752 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (152387/128000 : ℚ) (14139/16000 : ℚ) (58127/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_753 : Certificate start0_face1_leaf
    (planeBox (152387/128000 : ℚ) (76979/64000 : ℚ) (14139/16000 : ℚ) (58127/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_754 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (76979/64000 : ℚ) (14139/16000 : ℚ) (58127/64000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (152387/128000 : ℚ) (76979/64000 : ℚ) (14139/16000 : ℚ) (58127/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_752 start0_face1_node_753

theorem start0_face1_node_755 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (152387/128000 : ℚ) (58127/64000 : ℚ) (4713/5120 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_756 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (152387/128000 : ℚ) (4713/5120 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_757 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (152387/128000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (152387/128000 : ℚ) (58127/64000 : ℚ) (4713/5120 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_755 start0_face1_node_756

theorem start0_face1_node_758 : Certificate start0_face1_leaf
    (planeBox (152387/128000 : ℚ) (76979/64000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_759 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (76979/64000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (152387/128000 : ℚ) (76979/64000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_757 start0_face1_node_758

theorem start0_face1_node_760 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (76979/64000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (76979/64000 : ℚ) (14139/16000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_754 start0_face1_node_759

theorem start0_face1_node_761 : Certificate start0_face1_leaf
    (planeBox (76979/64000 : ℚ) (1571/1280 : ℚ) (14139/16000 : ℚ) (58127/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_762 : Certificate start0_face1_leaf
    (planeBox (76979/64000 : ℚ) (155529/128000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_763 : Certificate start0_face1_leaf
    (planeBox (155529/128000 : ℚ) (1571/1280 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_764 : Certificate start0_face1_leaf
    (planeBox (76979/64000 : ℚ) (1571/1280 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_zero (76979/64000 : ℚ) (155529/128000 : ℚ) (1571/1280 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_762 start0_face1_node_763

theorem start0_face1_node_765 : Certificate start0_face1_leaf
    (planeBox (76979/64000 : ℚ) (1571/1280 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_one (76979/64000 : ℚ) (1571/1280 : ℚ) (14139/16000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_761 start0_face1_node_764

theorem start0_face1_node_766 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (1571/1280 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (76979/64000 : ℚ) (1571/1280 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_760 start0_face1_node_765

theorem start0_face1_node_767 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (152387/128000 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_768 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (152387/128000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_769 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (152387/128000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (152387/128000 : ℚ) (29849/32000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_767 start0_face1_node_768

theorem start0_face1_node_770 : Certificate start0_face1_leaf
    (planeBox (152387/128000 : ℚ) (76979/64000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_771 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (76979/64000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (152387/128000 : ℚ) (76979/64000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_769 start0_face1_node_770

theorem start0_face1_node_772 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (152387/128000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_773 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (152387/128000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_774 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (152387/128000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (152387/128000 : ℚ) (61269/64000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_772 start0_face1_node_773

theorem start0_face1_node_775 : Certificate start0_face1_leaf
    (planeBox (152387/128000 : ℚ) (76979/64000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_776 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (76979/64000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (152387/128000 : ℚ) (76979/64000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_774 start0_face1_node_775

theorem start0_face1_node_777 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (76979/64000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (76979/64000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_771 start0_face1_node_776

theorem start0_face1_node_778 : Certificate start0_face1_leaf
    (planeBox (76979/64000 : ℚ) (155529/128000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_779 : Certificate start0_face1_leaf
    (planeBox (155529/128000 : ℚ) (1571/1280 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_780 : Certificate start0_face1_leaf
    (planeBox (76979/64000 : ℚ) (1571/1280 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ)) := by
  exact planeBox_split_zero (76979/64000 : ℚ) (155529/128000 : ℚ) (1571/1280 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_778 start0_face1_node_779

theorem start0_face1_node_781 : Certificate start0_face1_leaf
    (planeBox (76979/64000 : ℚ) (155529/128000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_782 : Certificate start0_face1_leaf
    (planeBox (155529/128000 : ℚ) (1571/1280 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_783 : Certificate start0_face1_leaf
    (planeBox (76979/64000 : ℚ) (1571/1280 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (76979/64000 : ℚ) (155529/128000 : ℚ) (1571/1280 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_781 start0_face1_node_782

theorem start0_face1_node_784 : Certificate start0_face1_leaf
    (planeBox (76979/64000 : ℚ) (1571/1280 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (76979/64000 : ℚ) (1571/1280 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_780 start0_face1_node_783

theorem start0_face1_node_785 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (1571/1280 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_zero (4713/4000 : ℚ) (76979/64000 : ℚ) (1571/1280 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_777 start0_face1_node_784

theorem start0_face1_node_786 : Certificate start0_face1_leaf
    (planeBox (4713/4000 : ℚ) (1571/1280 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact planeBox_split_one (4713/4000 : ℚ) (1571/1280 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_766 start0_face1_node_785

theorem start0_face1_node_787 : Certificate start0_face1_leaf
    (planeBox (1571/1280 : ℚ) (80121/64000 : ℚ) (14139/16000 : ℚ) (58127/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_788 : Certificate start0_face1_leaf
    (planeBox (1571/1280 : ℚ) (80121/64000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_789 : Certificate start0_face1_leaf
    (planeBox (1571/1280 : ℚ) (80121/64000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_one (1571/1280 : ℚ) (80121/64000 : ℚ) (14139/16000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_787 start0_face1_node_788

theorem start0_face1_node_790 : Certificate start0_face1_leaf
    (planeBox (80121/64000 : ℚ) (20423/16000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem start0_face1_node_791 : Certificate start0_face1_leaf
    (planeBox (1571/1280 : ℚ) (20423/16000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  exact planeBox_split_zero (1571/1280 : ℚ) (80121/64000 : ℚ) (20423/16000 : ℚ) (14139/16000 : ℚ) (29849/32000 : ℚ) (by norm_num) (by norm_num)
    start0_face1_node_789 start0_face1_node_790

theorem start0_face1_node_792 : Certificate start0_face1_leaf
    (planeBox (1571/1280 : ℚ) (80121/64000 : ℚ) (29849/32000 : ℚ) (61269/64000 : ℚ)) := by
  apply Certificate.accept
  unfold start0_face1_leaf
  apply Or.inr
  norm_num [start0_face1_p,start0_face1_q,start0_face1_b,start0_face1_bound,planeBox,planeDirectUpperQ,planeLinearCell,planeGradientUpperQ,planeGradientErrorQ,planeGradientCell,planeRadiusCell,faceRadiusCell,faceGradientCell,faceQuadraticGradientCell,SharedMomentFactorLocalGradientCertificate.next,SharedMomentFactorLocalGradientCertificate.prev,absBoundQ,planeCell,planeDomainCell,planeMidpointCell,faceDirectUpperQ,faceQuadraticCell,faceLinearCell,faceAngleLinearCell,sumThreeInterval,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RatInterval.sub,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.cosCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,RationalBoxSubdivision.midpoint,RationalBoxSubdivision.halfWidth,sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,CompactQuadraticMomentMaximum.maximumQ,CompactQuadraticArgmaxRange.lowerArgQ,CompactQuadraticArgmaxRange.upperArgQ,Finset.sum_range_succ,Fin.sum_univ_two,Fin.sum_univ_three,RatInterval.piLo,RatInterval.piHi,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

#print axioms start0_face1_node_792
end N11Formalization.SharedMomentConcreteFace1
