import N11Formalization.SharedMomentFactorIntervalCertificate

/-! A concrete complete-angle certificate from the saved exact nine-place
start-0 balanced-Q1 coefficients. Every closed leaf is checked with rational
Taylor arithmetic in the Lean kernel. This is one factor, not a class
exclusion or a global covering claim. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SharedMomentConcreteLeafControls
open RationalBoxSubdivision SharedMomentFactorIntervalCertificate
open SharedMomentFactorGridCertificate

def switchCell (lo hi : ℚ) : Cell (Fin 1) := fun _ => ⟨lo,hi⟩

theorem switchCell_split {leaf : Cell (Fin 1) → Prop} (lo mid hi : ℚ)
    (hlo : lo ≤ mid) (hhi : mid ≤ hi)
    (left : Certificate leaf (switchCell lo mid))
    (right : Certificate leaf (switchCell mid hi)) :
    Certificate leaf (switchCell lo hi) := by
  have hl : leftChild (switchCell lo hi) 0 mid = switchCell lo mid := by
    funext i
    fin_cases i
    simp [leftChild,switchCell]
  have hr : rightChild (switchCell lo hi) 0 mid = switchCell mid hi := by
    funext i
    fin_cases i
    simp [rightChild,switchCell]
  apply Certificate.split 0 mid hlo hhi
  · rw [hl]
    exact left
  · rw [hr]
    exact right

def start0_switch0_p : ℚ := (-2212383/62500000 : ℚ)
def start0_switch0_q : ℚ := (21538627/125000000 : ℚ)
def start0_switch0_b : ℚ := (-184795967/1000000000 : ℚ)
def start0_switch0_d2 : ℚ := (0 : ℚ)
def start0_switch0_d1 : ℚ := (0 : ℚ)
def start0_switch0_bound : ℚ := (1/2000 : ℚ)
def start0_switch0_leaf (B : Cell (Fin 1)) : Prop :=
  switchDirectUpperQ start0_switch0_p start0_switch0_q start0_switch0_b start0_switch0_d2 start0_switch0_d1 B ≤ start0_switch0_bound

theorem start0_switch0_node_0 : Certificate start0_switch0_leaf
    (switchCell (0 : ℚ) (1571/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_1 : Certificate start0_switch0_leaf
    (switchCell (1571/512000 : ℚ) (1571/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_2 : Certificate start0_switch0_leaf
    (switchCell (0 : ℚ) (1571/256000 : ℚ)) := by
  exact switchCell_split (0 : ℚ) (1571/512000 : ℚ) (1571/256000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_0 start0_switch0_node_1

theorem start0_switch0_node_3 : Certificate start0_switch0_leaf
    (switchCell (1571/256000 : ℚ) (1571/128000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_4 : Certificate start0_switch0_leaf
    (switchCell (0 : ℚ) (1571/128000 : ℚ)) := by
  exact switchCell_split (0 : ℚ) (1571/256000 : ℚ) (1571/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_2 start0_switch0_node_3

theorem start0_switch0_node_5 : Certificate start0_switch0_leaf
    (switchCell (1571/128000 : ℚ) (4713/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_6 : Certificate start0_switch0_leaf
    (switchCell (4713/256000 : ℚ) (1571/64000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_7 : Certificate start0_switch0_leaf
    (switchCell (1571/128000 : ℚ) (1571/64000 : ℚ)) := by
  exact switchCell_split (1571/128000 : ℚ) (4713/256000 : ℚ) (1571/64000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_5 start0_switch0_node_6

theorem start0_switch0_node_8 : Certificate start0_switch0_leaf
    (switchCell (0 : ℚ) (1571/64000 : ℚ)) := by
  exact switchCell_split (0 : ℚ) (1571/128000 : ℚ) (1571/64000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_4 start0_switch0_node_7

theorem start0_switch0_node_9 : Certificate start0_switch0_leaf
    (switchCell (1571/64000 : ℚ) (4713/128000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_10 : Certificate start0_switch0_leaf
    (switchCell (4713/128000 : ℚ) (1571/32000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_11 : Certificate start0_switch0_leaf
    (switchCell (1571/64000 : ℚ) (1571/32000 : ℚ)) := by
  exact switchCell_split (1571/64000 : ℚ) (4713/128000 : ℚ) (1571/32000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_9 start0_switch0_node_10

theorem start0_switch0_node_12 : Certificate start0_switch0_leaf
    (switchCell (0 : ℚ) (1571/32000 : ℚ)) := by
  exact switchCell_split (0 : ℚ) (1571/64000 : ℚ) (1571/32000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_8 start0_switch0_node_11

theorem start0_switch0_node_13 : Certificate start0_switch0_leaf
    (switchCell (1571/32000 : ℚ) (1571/25600 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_14 : Certificate start0_switch0_leaf
    (switchCell (1571/25600 : ℚ) (4713/64000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_15 : Certificate start0_switch0_leaf
    (switchCell (1571/32000 : ℚ) (4713/64000 : ℚ)) := by
  exact switchCell_split (1571/32000 : ℚ) (1571/25600 : ℚ) (4713/64000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_13 start0_switch0_node_14

theorem start0_switch0_node_16 : Certificate start0_switch0_leaf
    (switchCell (4713/64000 : ℚ) (1571/16000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_17 : Certificate start0_switch0_leaf
    (switchCell (1571/32000 : ℚ) (1571/16000 : ℚ)) := by
  exact switchCell_split (1571/32000 : ℚ) (4713/64000 : ℚ) (1571/16000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_15 start0_switch0_node_16

theorem start0_switch0_node_18 : Certificate start0_switch0_leaf
    (switchCell (0 : ℚ) (1571/16000 : ℚ)) := by
  exact switchCell_split (0 : ℚ) (1571/32000 : ℚ) (1571/16000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_12 start0_switch0_node_17

theorem start0_switch0_node_19 : Certificate start0_switch0_leaf
    (switchCell (1571/16000 : ℚ) (1571/12800 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_20 : Certificate start0_switch0_leaf
    (switchCell (1571/12800 : ℚ) (4713/32000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_21 : Certificate start0_switch0_leaf
    (switchCell (1571/16000 : ℚ) (4713/32000 : ℚ)) := by
  exact switchCell_split (1571/16000 : ℚ) (1571/12800 : ℚ) (4713/32000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_19 start0_switch0_node_20

theorem start0_switch0_node_22 : Certificate start0_switch0_leaf
    (switchCell (4713/32000 : ℚ) (10997/64000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_23 : Certificate start0_switch0_leaf
    (switchCell (10997/64000 : ℚ) (1571/8000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_24 : Certificate start0_switch0_leaf
    (switchCell (4713/32000 : ℚ) (1571/8000 : ℚ)) := by
  exact switchCell_split (4713/32000 : ℚ) (10997/64000 : ℚ) (1571/8000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_22 start0_switch0_node_23

theorem start0_switch0_node_25 : Certificate start0_switch0_leaf
    (switchCell (1571/16000 : ℚ) (1571/8000 : ℚ)) := by
  exact switchCell_split (1571/16000 : ℚ) (4713/32000 : ℚ) (1571/8000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_21 start0_switch0_node_24

theorem start0_switch0_node_26 : Certificate start0_switch0_leaf
    (switchCell (0 : ℚ) (1571/8000 : ℚ)) := by
  exact switchCell_split (0 : ℚ) (1571/16000 : ℚ) (1571/8000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_18 start0_switch0_node_25

theorem start0_switch0_node_27 : Certificate start0_switch0_leaf
    (switchCell (1571/8000 : ℚ) (14139/64000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_28 : Certificate start0_switch0_leaf
    (switchCell (14139/64000 : ℚ) (1571/6400 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_29 : Certificate start0_switch0_leaf
    (switchCell (1571/8000 : ℚ) (1571/6400 : ℚ)) := by
  exact switchCell_split (1571/8000 : ℚ) (14139/64000 : ℚ) (1571/6400 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_27 start0_switch0_node_28

theorem start0_switch0_node_30 : Certificate start0_switch0_leaf
    (switchCell (1571/6400 : ℚ) (17281/64000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_31 : Certificate start0_switch0_leaf
    (switchCell (17281/64000 : ℚ) (4713/16000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_32 : Certificate start0_switch0_leaf
    (switchCell (1571/6400 : ℚ) (4713/16000 : ℚ)) := by
  exact switchCell_split (1571/6400 : ℚ) (17281/64000 : ℚ) (4713/16000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_30 start0_switch0_node_31

theorem start0_switch0_node_33 : Certificate start0_switch0_leaf
    (switchCell (1571/8000 : ℚ) (4713/16000 : ℚ)) := by
  exact switchCell_split (1571/8000 : ℚ) (1571/6400 : ℚ) (4713/16000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_29 start0_switch0_node_32

theorem start0_switch0_node_34 : Certificate start0_switch0_leaf
    (switchCell (4713/16000 : ℚ) (20423/64000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_35 : Certificate start0_switch0_leaf
    (switchCell (20423/64000 : ℚ) (10997/32000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_36 : Certificate start0_switch0_leaf
    (switchCell (4713/16000 : ℚ) (10997/32000 : ℚ)) := by
  exact switchCell_split (4713/16000 : ℚ) (20423/64000 : ℚ) (10997/32000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_34 start0_switch0_node_35

theorem start0_switch0_node_37 : Certificate start0_switch0_leaf
    (switchCell (10997/32000 : ℚ) (4713/12800 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_38 : Certificate start0_switch0_leaf
    (switchCell (4713/12800 : ℚ) (1571/4000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_39 : Certificate start0_switch0_leaf
    (switchCell (10997/32000 : ℚ) (1571/4000 : ℚ)) := by
  exact switchCell_split (10997/32000 : ℚ) (4713/12800 : ℚ) (1571/4000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_37 start0_switch0_node_38

theorem start0_switch0_node_40 : Certificate start0_switch0_leaf
    (switchCell (4713/16000 : ℚ) (1571/4000 : ℚ)) := by
  exact switchCell_split (4713/16000 : ℚ) (10997/32000 : ℚ) (1571/4000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_36 start0_switch0_node_39

theorem start0_switch0_node_41 : Certificate start0_switch0_leaf
    (switchCell (1571/8000 : ℚ) (1571/4000 : ℚ)) := by
  exact switchCell_split (1571/8000 : ℚ) (4713/16000 : ℚ) (1571/4000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_33 start0_switch0_node_40

theorem start0_switch0_node_42 : Certificate start0_switch0_leaf
    (switchCell (0 : ℚ) (1571/4000 : ℚ)) := by
  exact switchCell_split (0 : ℚ) (1571/8000 : ℚ) (1571/4000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_26 start0_switch0_node_41

theorem start0_switch0_node_43 : Certificate start0_switch0_leaf
    (switchCell (1571/4000 : ℚ) (26707/64000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_44 : Certificate start0_switch0_leaf
    (switchCell (26707/64000 : ℚ) (14139/32000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_45 : Certificate start0_switch0_leaf
    (switchCell (1571/4000 : ℚ) (14139/32000 : ℚ)) := by
  exact switchCell_split (1571/4000 : ℚ) (26707/64000 : ℚ) (14139/32000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_43 start0_switch0_node_44

theorem start0_switch0_node_46 : Certificate start0_switch0_leaf
    (switchCell (14139/32000 : ℚ) (29849/64000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_47 : Certificate start0_switch0_leaf
    (switchCell (29849/64000 : ℚ) (1571/3200 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_48 : Certificate start0_switch0_leaf
    (switchCell (14139/32000 : ℚ) (1571/3200 : ℚ)) := by
  exact switchCell_split (14139/32000 : ℚ) (29849/64000 : ℚ) (1571/3200 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_46 start0_switch0_node_47

theorem start0_switch0_node_49 : Certificate start0_switch0_leaf
    (switchCell (1571/4000 : ℚ) (1571/3200 : ℚ)) := by
  exact switchCell_split (1571/4000 : ℚ) (14139/32000 : ℚ) (1571/3200 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_45 start0_switch0_node_48

theorem start0_switch0_node_50 : Certificate start0_switch0_leaf
    (switchCell (1571/3200 : ℚ) (64411/128000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_51 : Certificate start0_switch0_leaf
    (switchCell (64411/128000 : ℚ) (32991/64000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_52 : Certificate start0_switch0_leaf
    (switchCell (1571/3200 : ℚ) (32991/64000 : ℚ)) := by
  exact switchCell_split (1571/3200 : ℚ) (64411/128000 : ℚ) (32991/64000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_50 start0_switch0_node_51

theorem start0_switch0_node_53 : Certificate start0_switch0_leaf
    (switchCell (32991/64000 : ℚ) (67553/128000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_54 : Certificate start0_switch0_leaf
    (switchCell (67553/128000 : ℚ) (17281/32000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_55 : Certificate start0_switch0_leaf
    (switchCell (32991/64000 : ℚ) (17281/32000 : ℚ)) := by
  exact switchCell_split (32991/64000 : ℚ) (67553/128000 : ℚ) (17281/32000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_53 start0_switch0_node_54

theorem start0_switch0_node_56 : Certificate start0_switch0_leaf
    (switchCell (1571/3200 : ℚ) (17281/32000 : ℚ)) := by
  exact switchCell_split (1571/3200 : ℚ) (32991/64000 : ℚ) (17281/32000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_52 start0_switch0_node_55

theorem start0_switch0_node_57 : Certificate start0_switch0_leaf
    (switchCell (17281/32000 : ℚ) (14139/25600 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_58 : Certificate start0_switch0_leaf
    (switchCell (14139/25600 : ℚ) (36133/64000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_59 : Certificate start0_switch0_leaf
    (switchCell (17281/32000 : ℚ) (36133/64000 : ℚ)) := by
  exact switchCell_split (17281/32000 : ℚ) (14139/25600 : ℚ) (36133/64000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_57 start0_switch0_node_58

theorem start0_switch0_node_60 : Certificate start0_switch0_leaf
    (switchCell (36133/64000 : ℚ) (73837/128000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_61 : Certificate start0_switch0_leaf
    (switchCell (73837/128000 : ℚ) (4713/8000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_62 : Certificate start0_switch0_leaf
    (switchCell (36133/64000 : ℚ) (4713/8000 : ℚ)) := by
  exact switchCell_split (36133/64000 : ℚ) (73837/128000 : ℚ) (4713/8000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_60 start0_switch0_node_61

theorem start0_switch0_node_63 : Certificate start0_switch0_leaf
    (switchCell (17281/32000 : ℚ) (4713/8000 : ℚ)) := by
  exact switchCell_split (17281/32000 : ℚ) (36133/64000 : ℚ) (4713/8000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_59 start0_switch0_node_62

theorem start0_switch0_node_64 : Certificate start0_switch0_leaf
    (switchCell (1571/3200 : ℚ) (4713/8000 : ℚ)) := by
  exact switchCell_split (1571/3200 : ℚ) (17281/32000 : ℚ) (4713/8000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_56 start0_switch0_node_63

theorem start0_switch0_node_65 : Certificate start0_switch0_leaf
    (switchCell (1571/4000 : ℚ) (4713/8000 : ℚ)) := by
  exact switchCell_split (1571/4000 : ℚ) (1571/3200 : ℚ) (4713/8000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_49 start0_switch0_node_64

theorem start0_switch0_node_66 : Certificate start0_switch0_leaf
    (switchCell (4713/8000 : ℚ) (76979/128000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_67 : Certificate start0_switch0_leaf
    (switchCell (76979/128000 : ℚ) (1571/2560 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_68 : Certificate start0_switch0_leaf
    (switchCell (4713/8000 : ℚ) (1571/2560 : ℚ)) := by
  exact switchCell_split (4713/8000 : ℚ) (76979/128000 : ℚ) (1571/2560 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_66 start0_switch0_node_67

theorem start0_switch0_node_69 : Certificate start0_switch0_leaf
    (switchCell (1571/2560 : ℚ) (158671/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_70 : Certificate start0_switch0_leaf
    (switchCell (158671/256000 : ℚ) (80121/128000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_71 : Certificate start0_switch0_leaf
    (switchCell (1571/2560 : ℚ) (80121/128000 : ℚ)) := by
  exact switchCell_split (1571/2560 : ℚ) (158671/256000 : ℚ) (80121/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_69 start0_switch0_node_70

theorem start0_switch0_node_72 : Certificate start0_switch0_leaf
    (switchCell (80121/128000 : ℚ) (161813/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_73 : Certificate start0_switch0_leaf
    (switchCell (161813/256000 : ℚ) (20423/32000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_74 : Certificate start0_switch0_leaf
    (switchCell (80121/128000 : ℚ) (20423/32000 : ℚ)) := by
  exact switchCell_split (80121/128000 : ℚ) (161813/256000 : ℚ) (20423/32000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_72 start0_switch0_node_73

theorem start0_switch0_node_75 : Certificate start0_switch0_leaf
    (switchCell (1571/2560 : ℚ) (20423/32000 : ℚ)) := by
  exact switchCell_split (1571/2560 : ℚ) (80121/128000 : ℚ) (20423/32000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_71 start0_switch0_node_74

theorem start0_switch0_node_76 : Certificate start0_switch0_leaf
    (switchCell (4713/8000 : ℚ) (20423/32000 : ℚ)) := by
  exact switchCell_split (4713/8000 : ℚ) (1571/2560 : ℚ) (20423/32000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_68 start0_switch0_node_75

theorem start0_switch0_node_77 : Certificate start0_switch0_leaf
    (switchCell (20423/32000 : ℚ) (32991/51200 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_78 : Certificate start0_switch0_leaf
    (switchCell (32991/51200 : ℚ) (83263/128000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_79 : Certificate start0_switch0_leaf
    (switchCell (20423/32000 : ℚ) (83263/128000 : ℚ)) := by
  exact switchCell_split (20423/32000 : ℚ) (32991/51200 : ℚ) (83263/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_77 start0_switch0_node_78

theorem start0_switch0_node_80 : Certificate start0_switch0_leaf
    (switchCell (83263/128000 : ℚ) (168097/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_81 : Certificate start0_switch0_leaf
    (switchCell (168097/256000 : ℚ) (42417/64000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_82 : Certificate start0_switch0_leaf
    (switchCell (83263/128000 : ℚ) (42417/64000 : ℚ)) := by
  exact switchCell_split (83263/128000 : ℚ) (168097/256000 : ℚ) (42417/64000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_80 start0_switch0_node_81

theorem start0_switch0_node_83 : Certificate start0_switch0_leaf
    (switchCell (20423/32000 : ℚ) (42417/64000 : ℚ)) := by
  exact switchCell_split (20423/32000 : ℚ) (83263/128000 : ℚ) (42417/64000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_79 start0_switch0_node_82

theorem start0_switch0_node_84 : Certificate start0_switch0_leaf
    (switchCell (42417/64000 : ℚ) (171239/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_85 : Certificate start0_switch0_leaf
    (switchCell (171239/256000 : ℚ) (17281/25600 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_86 : Certificate start0_switch0_leaf
    (switchCell (42417/64000 : ℚ) (17281/25600 : ℚ)) := by
  exact switchCell_split (42417/64000 : ℚ) (171239/256000 : ℚ) (17281/25600 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_84 start0_switch0_node_85

theorem start0_switch0_node_87 : Certificate start0_switch0_leaf
    (switchCell (17281/25600 : ℚ) (174381/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_88 : Certificate start0_switch0_leaf
    (switchCell (174381/256000 : ℚ) (10997/16000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_89 : Certificate start0_switch0_leaf
    (switchCell (17281/25600 : ℚ) (10997/16000 : ℚ)) := by
  exact switchCell_split (17281/25600 : ℚ) (174381/256000 : ℚ) (10997/16000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_87 start0_switch0_node_88

theorem start0_switch0_node_90 : Certificate start0_switch0_leaf
    (switchCell (42417/64000 : ℚ) (10997/16000 : ℚ)) := by
  exact switchCell_split (42417/64000 : ℚ) (17281/25600 : ℚ) (10997/16000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_86 start0_switch0_node_89

theorem start0_switch0_node_91 : Certificate start0_switch0_leaf
    (switchCell (20423/32000 : ℚ) (10997/16000 : ℚ)) := by
  exact switchCell_split (20423/32000 : ℚ) (42417/64000 : ℚ) (10997/16000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_83 start0_switch0_node_90

theorem start0_switch0_node_92 : Certificate start0_switch0_leaf
    (switchCell (4713/8000 : ℚ) (10997/16000 : ℚ)) := by
  exact switchCell_split (4713/8000 : ℚ) (20423/32000 : ℚ) (10997/16000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_76 start0_switch0_node_91

theorem start0_switch0_node_93 : Certificate start0_switch0_leaf
    (switchCell (10997/16000 : ℚ) (177523/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_94 : Certificate start0_switch0_leaf
    (switchCell (177523/256000 : ℚ) (356617/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_95 : Certificate start0_switch0_leaf
    (switchCell (356617/512000 : ℚ) (89547/128000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_96 : Certificate start0_switch0_leaf
    (switchCell (177523/256000 : ℚ) (89547/128000 : ℚ)) := by
  exact switchCell_split (177523/256000 : ℚ) (356617/512000 : ℚ) (89547/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_94 start0_switch0_node_95

theorem start0_switch0_node_97 : Certificate start0_switch0_leaf
    (switchCell (10997/16000 : ℚ) (89547/128000 : ℚ)) := by
  exact switchCell_split (10997/16000 : ℚ) (177523/256000 : ℚ) (89547/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_93 start0_switch0_node_96

theorem start0_switch0_node_98 : Certificate start0_switch0_leaf
    (switchCell (89547/128000 : ℚ) (359759/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_99 : Certificate start0_switch0_leaf
    (switchCell (359759/512000 : ℚ) (36133/51200 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_100 : Certificate start0_switch0_leaf
    (switchCell (89547/128000 : ℚ) (36133/51200 : ℚ)) := by
  exact switchCell_split (89547/128000 : ℚ) (359759/512000 : ℚ) (36133/51200 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_98 start0_switch0_node_99

theorem start0_switch0_node_101 : Certificate start0_switch0_leaf
    (switchCell (36133/51200 : ℚ) (362901/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_102 : Certificate start0_switch0_leaf
    (switchCell (362901/512000 : ℚ) (45559/64000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_103 : Certificate start0_switch0_leaf
    (switchCell (36133/51200 : ℚ) (45559/64000 : ℚ)) := by
  exact switchCell_split (36133/51200 : ℚ) (362901/512000 : ℚ) (45559/64000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_101 start0_switch0_node_102

theorem start0_switch0_node_104 : Certificate start0_switch0_leaf
    (switchCell (89547/128000 : ℚ) (45559/64000 : ℚ)) := by
  exact switchCell_split (89547/128000 : ℚ) (36133/51200 : ℚ) (45559/64000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_100 start0_switch0_node_103

theorem start0_switch0_node_105 : Certificate start0_switch0_leaf
    (switchCell (10997/16000 : ℚ) (45559/64000 : ℚ)) := by
  exact switchCell_split (10997/16000 : ℚ) (89547/128000 : ℚ) (45559/64000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_97 start0_switch0_node_104

theorem start0_switch0_node_106 : Certificate start0_switch0_leaf
    (switchCell (45559/64000 : ℚ) (366043/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_107 : Certificate start0_switch0_leaf
    (switchCell (366043/512000 : ℚ) (183807/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_108 : Certificate start0_switch0_leaf
    (switchCell (45559/64000 : ℚ) (183807/256000 : ℚ)) := by
  exact switchCell_split (45559/64000 : ℚ) (366043/512000 : ℚ) (183807/256000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_106 start0_switch0_node_107

theorem start0_switch0_node_109 : Certificate start0_switch0_leaf
    (switchCell (183807/256000 : ℚ) (73837/102400 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_110 : Certificate start0_switch0_leaf
    (switchCell (73837/102400 : ℚ) (92689/128000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_111 : Certificate start0_switch0_leaf
    (switchCell (183807/256000 : ℚ) (92689/128000 : ℚ)) := by
  exact switchCell_split (183807/256000 : ℚ) (73837/102400 : ℚ) (92689/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_109 start0_switch0_node_110

theorem start0_switch0_node_112 : Certificate start0_switch0_leaf
    (switchCell (45559/64000 : ℚ) (92689/128000 : ℚ)) := by
  exact switchCell_split (45559/64000 : ℚ) (183807/256000 : ℚ) (92689/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_108 start0_switch0_node_111

theorem start0_switch0_node_113 : Certificate start0_switch0_leaf
    (switchCell (92689/128000 : ℚ) (372327/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_114 : Certificate start0_switch0_leaf
    (switchCell (372327/512000 : ℚ) (186949/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_115 : Certificate start0_switch0_leaf
    (switchCell (92689/128000 : ℚ) (186949/256000 : ℚ)) := by
  exact switchCell_split (92689/128000 : ℚ) (372327/512000 : ℚ) (186949/256000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_113 start0_switch0_node_114

theorem start0_switch0_node_116 : Certificate start0_switch0_leaf
    (switchCell (186949/256000 : ℚ) (375469/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_117 : Certificate start0_switch0_leaf
    (switchCell (375469/512000 : ℚ) (4713/6400 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_118 : Certificate start0_switch0_leaf
    (switchCell (186949/256000 : ℚ) (4713/6400 : ℚ)) := by
  exact switchCell_split (186949/256000 : ℚ) (375469/512000 : ℚ) (4713/6400 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_116 start0_switch0_node_117

theorem start0_switch0_node_119 : Certificate start0_switch0_leaf
    (switchCell (92689/128000 : ℚ) (4713/6400 : ℚ)) := by
  exact switchCell_split (92689/128000 : ℚ) (186949/256000 : ℚ) (4713/6400 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_115 start0_switch0_node_118

theorem start0_switch0_node_120 : Certificate start0_switch0_leaf
    (switchCell (45559/64000 : ℚ) (4713/6400 : ℚ)) := by
  exact switchCell_split (45559/64000 : ℚ) (92689/128000 : ℚ) (4713/6400 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_112 start0_switch0_node_119

theorem start0_switch0_node_121 : Certificate start0_switch0_leaf
    (switchCell (10997/16000 : ℚ) (4713/6400 : ℚ)) := by
  exact switchCell_split (10997/16000 : ℚ) (45559/64000 : ℚ) (4713/6400 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_105 start0_switch0_node_120

theorem start0_switch0_node_122 : Certificate start0_switch0_leaf
    (switchCell (4713/6400 : ℚ) (378611/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_123 : Certificate start0_switch0_leaf
    (switchCell (378611/512000 : ℚ) (190091/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_124 : Certificate start0_switch0_leaf
    (switchCell (4713/6400 : ℚ) (190091/256000 : ℚ)) := by
  exact switchCell_split (4713/6400 : ℚ) (378611/512000 : ℚ) (190091/256000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_122 start0_switch0_node_123

theorem start0_switch0_node_125 : Certificate start0_switch0_leaf
    (switchCell (190091/256000 : ℚ) (381753/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_126 : Certificate start0_switch0_leaf
    (switchCell (381753/512000 : ℚ) (95831/128000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_127 : Certificate start0_switch0_leaf
    (switchCell (190091/256000 : ℚ) (95831/128000 : ℚ)) := by
  exact switchCell_split (190091/256000 : ℚ) (381753/512000 : ℚ) (95831/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_125 start0_switch0_node_126

theorem start0_switch0_node_128 : Certificate start0_switch0_leaf
    (switchCell (4713/6400 : ℚ) (95831/128000 : ℚ)) := by
  exact switchCell_split (4713/6400 : ℚ) (190091/256000 : ℚ) (95831/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_124 start0_switch0_node_127

theorem start0_switch0_node_129 : Certificate start0_switch0_leaf
    (switchCell (95831/128000 : ℚ) (76979/102400 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_130 : Certificate start0_switch0_leaf
    (switchCell (76979/102400 : ℚ) (193233/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_131 : Certificate start0_switch0_leaf
    (switchCell (95831/128000 : ℚ) (193233/256000 : ℚ)) := by
  exact switchCell_split (95831/128000 : ℚ) (76979/102400 : ℚ) (193233/256000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_129 start0_switch0_node_130

theorem start0_switch0_node_132 : Certificate start0_switch0_leaf
    (switchCell (193233/256000 : ℚ) (388037/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_133 : Certificate start0_switch0_leaf
    (switchCell (388037/512000 : ℚ) (48701/64000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_134 : Certificate start0_switch0_leaf
    (switchCell (193233/256000 : ℚ) (48701/64000 : ℚ)) := by
  exact switchCell_split (193233/256000 : ℚ) (388037/512000 : ℚ) (48701/64000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_132 start0_switch0_node_133

theorem start0_switch0_node_135 : Certificate start0_switch0_leaf
    (switchCell (95831/128000 : ℚ) (48701/64000 : ℚ)) := by
  exact switchCell_split (95831/128000 : ℚ) (193233/256000 : ℚ) (48701/64000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_131 start0_switch0_node_134

theorem start0_switch0_node_136 : Certificate start0_switch0_leaf
    (switchCell (4713/6400 : ℚ) (48701/64000 : ℚ)) := by
  exact switchCell_split (4713/6400 : ℚ) (95831/128000 : ℚ) (48701/64000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_128 start0_switch0_node_135

theorem start0_switch0_node_137 : Certificate start0_switch0_leaf
    (switchCell (48701/64000 : ℚ) (391179/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_138 : Certificate start0_switch0_leaf
    (switchCell (391179/512000 : ℚ) (1571/2048 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_139 : Certificate start0_switch0_leaf
    (switchCell (48701/64000 : ℚ) (1571/2048 : ℚ)) := by
  exact switchCell_split (48701/64000 : ℚ) (391179/512000 : ℚ) (1571/2048 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_137 start0_switch0_node_138

theorem start0_switch0_node_140 : Certificate start0_switch0_leaf
    (switchCell (1571/2048 : ℚ) (787071/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_141 : Certificate start0_switch0_leaf
    (switchCell (787071/1024000 : ℚ) (394321/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_142 : Certificate start0_switch0_leaf
    (switchCell (1571/2048 : ℚ) (394321/512000 : ℚ)) := by
  exact switchCell_split (1571/2048 : ℚ) (787071/1024000 : ℚ) (394321/512000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_140 start0_switch0_node_141

theorem start0_switch0_node_143 : Certificate start0_switch0_leaf
    (switchCell (394321/512000 : ℚ) (790213/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_144 : Certificate start0_switch0_leaf
    (switchCell (790213/1024000 : ℚ) (98973/128000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_145 : Certificate start0_switch0_leaf
    (switchCell (394321/512000 : ℚ) (98973/128000 : ℚ)) := by
  exact switchCell_split (394321/512000 : ℚ) (790213/1024000 : ℚ) (98973/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_143 start0_switch0_node_144

theorem start0_switch0_node_146 : Certificate start0_switch0_leaf
    (switchCell (1571/2048 : ℚ) (98973/128000 : ℚ)) := by
  exact switchCell_split (1571/2048 : ℚ) (394321/512000 : ℚ) (98973/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_142 start0_switch0_node_145

theorem start0_switch0_node_147 : Certificate start0_switch0_leaf
    (switchCell (48701/64000 : ℚ) (98973/128000 : ℚ)) := by
  exact switchCell_split (48701/64000 : ℚ) (1571/2048 : ℚ) (98973/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_139 start0_switch0_node_146

theorem start0_switch0_node_148 : Certificate start0_switch0_leaf
    (switchCell (98973/128000 : ℚ) (158671/204800 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_149 : Certificate start0_switch0_leaf
    (switchCell (158671/204800 : ℚ) (397463/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_150 : Certificate start0_switch0_leaf
    (switchCell (98973/128000 : ℚ) (397463/512000 : ℚ)) := by
  exact switchCell_split (98973/128000 : ℚ) (158671/204800 : ℚ) (397463/512000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_148 start0_switch0_node_149

theorem start0_switch0_node_151 : Certificate start0_switch0_leaf
    (switchCell (397463/512000 : ℚ) (796497/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_152 : Certificate start0_switch0_leaf
    (switchCell (796497/1024000 : ℚ) (199517/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_153 : Certificate start0_switch0_leaf
    (switchCell (397463/512000 : ℚ) (199517/256000 : ℚ)) := by
  exact switchCell_split (397463/512000 : ℚ) (796497/1024000 : ℚ) (199517/256000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_151 start0_switch0_node_152

theorem start0_switch0_node_154 : Certificate start0_switch0_leaf
    (switchCell (98973/128000 : ℚ) (199517/256000 : ℚ)) := by
  exact switchCell_split (98973/128000 : ℚ) (397463/512000 : ℚ) (199517/256000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_150 start0_switch0_node_153

theorem start0_switch0_node_155 : Certificate start0_switch0_leaf
    (switchCell (199517/256000 : ℚ) (799639/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_156 : Certificate start0_switch0_leaf
    (switchCell (799639/1024000 : ℚ) (80121/102400 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_157 : Certificate start0_switch0_leaf
    (switchCell (199517/256000 : ℚ) (80121/102400 : ℚ)) := by
  exact switchCell_split (199517/256000 : ℚ) (799639/1024000 : ℚ) (80121/102400 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_155 start0_switch0_node_156

theorem start0_switch0_node_158 : Certificate start0_switch0_leaf
    (switchCell (80121/102400 : ℚ) (802781/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_159 : Certificate start0_switch0_leaf
    (switchCell (802781/1024000 : ℚ) (1571/2000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_160 : Certificate start0_switch0_leaf
    (switchCell (80121/102400 : ℚ) (1571/2000 : ℚ)) := by
  exact switchCell_split (80121/102400 : ℚ) (802781/1024000 : ℚ) (1571/2000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_158 start0_switch0_node_159

theorem start0_switch0_node_161 : Certificate start0_switch0_leaf
    (switchCell (199517/256000 : ℚ) (1571/2000 : ℚ)) := by
  exact switchCell_split (199517/256000 : ℚ) (80121/102400 : ℚ) (1571/2000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_157 start0_switch0_node_160

theorem start0_switch0_node_162 : Certificate start0_switch0_leaf
    (switchCell (98973/128000 : ℚ) (1571/2000 : ℚ)) := by
  exact switchCell_split (98973/128000 : ℚ) (199517/256000 : ℚ) (1571/2000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_154 start0_switch0_node_161

theorem start0_switch0_node_163 : Certificate start0_switch0_leaf
    (switchCell (48701/64000 : ℚ) (1571/2000 : ℚ)) := by
  exact switchCell_split (48701/64000 : ℚ) (98973/128000 : ℚ) (1571/2000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_147 start0_switch0_node_162

theorem start0_switch0_node_164 : Certificate start0_switch0_leaf
    (switchCell (4713/6400 : ℚ) (1571/2000 : ℚ)) := by
  exact switchCell_split (4713/6400 : ℚ) (48701/64000 : ℚ) (1571/2000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_136 start0_switch0_node_163

theorem start0_switch0_node_165 : Certificate start0_switch0_leaf
    (switchCell (10997/16000 : ℚ) (1571/2000 : ℚ)) := by
  exact switchCell_split (10997/16000 : ℚ) (4713/6400 : ℚ) (1571/2000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_121 start0_switch0_node_164

theorem start0_switch0_node_166 : Certificate start0_switch0_leaf
    (switchCell (4713/8000 : ℚ) (1571/2000 : ℚ)) := by
  exact switchCell_split (4713/8000 : ℚ) (10997/16000 : ℚ) (1571/2000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_92 start0_switch0_node_165

theorem start0_switch0_node_167 : Certificate start0_switch0_leaf
    (switchCell (1571/4000 : ℚ) (1571/2000 : ℚ)) := by
  exact switchCell_split (1571/4000 : ℚ) (4713/8000 : ℚ) (1571/2000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_65 start0_switch0_node_166

theorem start0_switch0_node_168 : Certificate start0_switch0_leaf
    (switchCell (0 : ℚ) (1571/2000 : ℚ)) := by
  exact switchCell_split (0 : ℚ) (1571/4000 : ℚ) (1571/2000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_42 start0_switch0_node_167

theorem start0_switch0_node_169 : Certificate start0_switch0_leaf
    (switchCell (1571/2000 : ℚ) (805923/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_170 : Certificate start0_switch0_leaf
    (switchCell (805923/1024000 : ℚ) (403747/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_171 : Certificate start0_switch0_leaf
    (switchCell (1571/2000 : ℚ) (403747/512000 : ℚ)) := by
  exact switchCell_split (1571/2000 : ℚ) (805923/1024000 : ℚ) (403747/512000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_169 start0_switch0_node_170

theorem start0_switch0_node_172 : Certificate start0_switch0_leaf
    (switchCell (403747/512000 : ℚ) (161813/204800 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_173 : Certificate start0_switch0_leaf
    (switchCell (161813/204800 : ℚ) (202659/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_174 : Certificate start0_switch0_leaf
    (switchCell (403747/512000 : ℚ) (202659/256000 : ℚ)) := by
  exact switchCell_split (403747/512000 : ℚ) (161813/204800 : ℚ) (202659/256000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_172 start0_switch0_node_173

theorem start0_switch0_node_175 : Certificate start0_switch0_leaf
    (switchCell (1571/2000 : ℚ) (202659/256000 : ℚ)) := by
  exact switchCell_split (1571/2000 : ℚ) (403747/512000 : ℚ) (202659/256000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_171 start0_switch0_node_174

theorem start0_switch0_node_176 : Certificate start0_switch0_leaf
    (switchCell (202659/256000 : ℚ) (812207/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_177 : Certificate start0_switch0_leaf
    (switchCell (812207/1024000 : ℚ) (406889/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_178 : Certificate start0_switch0_leaf
    (switchCell (202659/256000 : ℚ) (406889/512000 : ℚ)) := by
  exact switchCell_split (202659/256000 : ℚ) (812207/1024000 : ℚ) (406889/512000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_176 start0_switch0_node_177

theorem start0_switch0_node_179 : Certificate start0_switch0_leaf
    (switchCell (406889/512000 : ℚ) (815349/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_180 : Certificate start0_switch0_leaf
    (switchCell (815349/1024000 : ℚ) (20423/25600 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_181 : Certificate start0_switch0_leaf
    (switchCell (406889/512000 : ℚ) (20423/25600 : ℚ)) := by
  exact switchCell_split (406889/512000 : ℚ) (815349/1024000 : ℚ) (20423/25600 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_179 start0_switch0_node_180

theorem start0_switch0_node_182 : Certificate start0_switch0_leaf
    (switchCell (202659/256000 : ℚ) (20423/25600 : ℚ)) := by
  exact switchCell_split (202659/256000 : ℚ) (406889/512000 : ℚ) (20423/25600 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_178 start0_switch0_node_181

theorem start0_switch0_node_183 : Certificate start0_switch0_leaf
    (switchCell (1571/2000 : ℚ) (20423/25600 : ℚ)) := by
  exact switchCell_split (1571/2000 : ℚ) (202659/256000 : ℚ) (20423/25600 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_175 start0_switch0_node_182

theorem start0_switch0_node_184 : Certificate start0_switch0_leaf
    (switchCell (20423/25600 : ℚ) (818491/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_185 : Certificate start0_switch0_leaf
    (switchCell (818491/1024000 : ℚ) (410031/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_186 : Certificate start0_switch0_leaf
    (switchCell (20423/25600 : ℚ) (410031/512000 : ℚ)) := by
  exact switchCell_split (20423/25600 : ℚ) (818491/1024000 : ℚ) (410031/512000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_184 start0_switch0_node_185

theorem start0_switch0_node_187 : Certificate start0_switch0_leaf
    (switchCell (410031/512000 : ℚ) (821633/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_188 : Certificate start0_switch0_leaf
    (switchCell (821633/1024000 : ℚ) (205801/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_189 : Certificate start0_switch0_leaf
    (switchCell (410031/512000 : ℚ) (205801/256000 : ℚ)) := by
  exact switchCell_split (410031/512000 : ℚ) (821633/1024000 : ℚ) (205801/256000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_187 start0_switch0_node_188

theorem start0_switch0_node_190 : Certificate start0_switch0_leaf
    (switchCell (20423/25600 : ℚ) (205801/256000 : ℚ)) := by
  exact switchCell_split (20423/25600 : ℚ) (410031/512000 : ℚ) (205801/256000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_186 start0_switch0_node_189

theorem start0_switch0_node_191 : Certificate start0_switch0_leaf
    (switchCell (205801/256000 : ℚ) (32991/40960 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_192 : Certificate start0_switch0_leaf
    (switchCell (32991/40960 : ℚ) (413173/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_193 : Certificate start0_switch0_leaf
    (switchCell (205801/256000 : ℚ) (413173/512000 : ℚ)) := by
  exact switchCell_split (205801/256000 : ℚ) (32991/40960 : ℚ) (413173/512000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_191 start0_switch0_node_192

theorem start0_switch0_node_194 : Certificate start0_switch0_leaf
    (switchCell (413173/512000 : ℚ) (827917/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_195 : Certificate start0_switch0_leaf
    (switchCell (827917/1024000 : ℚ) (51843/64000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_196 : Certificate start0_switch0_leaf
    (switchCell (413173/512000 : ℚ) (51843/64000 : ℚ)) := by
  exact switchCell_split (413173/512000 : ℚ) (827917/1024000 : ℚ) (51843/64000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_194 start0_switch0_node_195

theorem start0_switch0_node_197 : Certificate start0_switch0_leaf
    (switchCell (205801/256000 : ℚ) (51843/64000 : ℚ)) := by
  exact switchCell_split (205801/256000 : ℚ) (413173/512000 : ℚ) (51843/64000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_193 start0_switch0_node_196

theorem start0_switch0_node_198 : Certificate start0_switch0_leaf
    (switchCell (20423/25600 : ℚ) (51843/64000 : ℚ)) := by
  exact switchCell_split (20423/25600 : ℚ) (205801/256000 : ℚ) (51843/64000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_190 start0_switch0_node_197

theorem start0_switch0_node_199 : Certificate start0_switch0_leaf
    (switchCell (1571/2000 : ℚ) (51843/64000 : ℚ)) := by
  exact switchCell_split (1571/2000 : ℚ) (20423/25600 : ℚ) (51843/64000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_183 start0_switch0_node_198

theorem start0_switch0_node_200 : Certificate start0_switch0_leaf
    (switchCell (51843/64000 : ℚ) (831059/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_201 : Certificate start0_switch0_leaf
    (switchCell (831059/1024000 : ℚ) (83263/102400 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_202 : Certificate start0_switch0_leaf
    (switchCell (51843/64000 : ℚ) (83263/102400 : ℚ)) := by
  exact switchCell_split (51843/64000 : ℚ) (831059/1024000 : ℚ) (83263/102400 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_200 start0_switch0_node_201

theorem start0_switch0_node_203 : Certificate start0_switch0_leaf
    (switchCell (83263/102400 : ℚ) (834201/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_204 : Certificate start0_switch0_leaf
    (switchCell (834201/1024000 : ℚ) (208943/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_205 : Certificate start0_switch0_leaf
    (switchCell (83263/102400 : ℚ) (208943/256000 : ℚ)) := by
  exact switchCell_split (83263/102400 : ℚ) (834201/1024000 : ℚ) (208943/256000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_203 start0_switch0_node_204

theorem start0_switch0_node_206 : Certificate start0_switch0_leaf
    (switchCell (51843/64000 : ℚ) (208943/256000 : ℚ)) := by
  exact switchCell_split (51843/64000 : ℚ) (83263/102400 : ℚ) (208943/256000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_202 start0_switch0_node_205

theorem start0_switch0_node_207 : Certificate start0_switch0_leaf
    (switchCell (208943/256000 : ℚ) (837343/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_208 : Certificate start0_switch0_leaf
    (switchCell (837343/1024000 : ℚ) (419457/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_209 : Certificate start0_switch0_leaf
    (switchCell (208943/256000 : ℚ) (419457/512000 : ℚ)) := by
  exact switchCell_split (208943/256000 : ℚ) (837343/1024000 : ℚ) (419457/512000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_207 start0_switch0_node_208

theorem start0_switch0_node_210 : Certificate start0_switch0_leaf
    (switchCell (419457/512000 : ℚ) (168097/204800 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_211 : Certificate start0_switch0_leaf
    (switchCell (168097/204800 : ℚ) (105257/128000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_212 : Certificate start0_switch0_leaf
    (switchCell (419457/512000 : ℚ) (105257/128000 : ℚ)) := by
  exact switchCell_split (419457/512000 : ℚ) (168097/204800 : ℚ) (105257/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_210 start0_switch0_node_211

theorem start0_switch0_node_213 : Certificate start0_switch0_leaf
    (switchCell (208943/256000 : ℚ) (105257/128000 : ℚ)) := by
  exact switchCell_split (208943/256000 : ℚ) (419457/512000 : ℚ) (105257/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_209 start0_switch0_node_212

theorem start0_switch0_node_214 : Certificate start0_switch0_leaf
    (switchCell (51843/64000 : ℚ) (105257/128000 : ℚ)) := by
  exact switchCell_split (51843/64000 : ℚ) (208943/256000 : ℚ) (105257/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_206 start0_switch0_node_213

theorem start0_switch0_node_215 : Certificate start0_switch0_leaf
    (switchCell (105257/128000 : ℚ) (843627/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_216 : Certificate start0_switch0_leaf
    (switchCell (843627/1024000 : ℚ) (422599/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_217 : Certificate start0_switch0_leaf
    (switchCell (105257/128000 : ℚ) (422599/512000 : ℚ)) := by
  exact switchCell_split (105257/128000 : ℚ) (843627/1024000 : ℚ) (422599/512000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_215 start0_switch0_node_216

theorem start0_switch0_node_218 : Certificate start0_switch0_leaf
    (switchCell (422599/512000 : ℚ) (846769/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_219 : Certificate start0_switch0_leaf
    (switchCell (846769/1024000 : ℚ) (42417/51200 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_220 : Certificate start0_switch0_leaf
    (switchCell (422599/512000 : ℚ) (42417/51200 : ℚ)) := by
  exact switchCell_split (422599/512000 : ℚ) (846769/1024000 : ℚ) (42417/51200 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_218 start0_switch0_node_219

theorem start0_switch0_node_221 : Certificate start0_switch0_leaf
    (switchCell (105257/128000 : ℚ) (42417/51200 : ℚ)) := by
  exact switchCell_split (105257/128000 : ℚ) (422599/512000 : ℚ) (42417/51200 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_217 start0_switch0_node_220

theorem start0_switch0_node_222 : Certificate start0_switch0_leaf
    (switchCell (42417/51200 : ℚ) (849911/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_223 : Certificate start0_switch0_leaf
    (switchCell (849911/1024000 : ℚ) (425741/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_224 : Certificate start0_switch0_leaf
    (switchCell (42417/51200 : ℚ) (425741/512000 : ℚ)) := by
  exact switchCell_split (42417/51200 : ℚ) (849911/1024000 : ℚ) (425741/512000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_222 start0_switch0_node_223

theorem start0_switch0_node_225 : Certificate start0_switch0_leaf
    (switchCell (425741/512000 : ℚ) (853053/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_226 : Certificate start0_switch0_leaf
    (switchCell (853053/1024000 : ℚ) (26707/32000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_227 : Certificate start0_switch0_leaf
    (switchCell (425741/512000 : ℚ) (26707/32000 : ℚ)) := by
  exact switchCell_split (425741/512000 : ℚ) (853053/1024000 : ℚ) (26707/32000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_225 start0_switch0_node_226

theorem start0_switch0_node_228 : Certificate start0_switch0_leaf
    (switchCell (42417/51200 : ℚ) (26707/32000 : ℚ)) := by
  exact switchCell_split (42417/51200 : ℚ) (425741/512000 : ℚ) (26707/32000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_224 start0_switch0_node_227

theorem start0_switch0_node_229 : Certificate start0_switch0_leaf
    (switchCell (105257/128000 : ℚ) (26707/32000 : ℚ)) := by
  exact switchCell_split (105257/128000 : ℚ) (42417/51200 : ℚ) (26707/32000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_221 start0_switch0_node_228

theorem start0_switch0_node_230 : Certificate start0_switch0_leaf
    (switchCell (51843/64000 : ℚ) (26707/32000 : ℚ)) := by
  exact switchCell_split (51843/64000 : ℚ) (105257/128000 : ℚ) (26707/32000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_214 start0_switch0_node_229

theorem start0_switch0_node_231 : Certificate start0_switch0_leaf
    (switchCell (1571/2000 : ℚ) (26707/32000 : ℚ)) := by
  exact switchCell_split (1571/2000 : ℚ) (51843/64000 : ℚ) (26707/32000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_199 start0_switch0_node_230

theorem start0_switch0_node_232 : Certificate start0_switch0_leaf
    (switchCell (26707/32000 : ℚ) (171239/204800 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_233 : Certificate start0_switch0_leaf
    (switchCell (171239/204800 : ℚ) (428883/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_234 : Certificate start0_switch0_leaf
    (switchCell (26707/32000 : ℚ) (428883/512000 : ℚ)) := by
  exact switchCell_split (26707/32000 : ℚ) (171239/204800 : ℚ) (428883/512000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_232 start0_switch0_node_233

theorem start0_switch0_node_235 : Certificate start0_switch0_leaf
    (switchCell (428883/512000 : ℚ) (859337/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_236 : Certificate start0_switch0_leaf
    (switchCell (859337/1024000 : ℚ) (215227/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_237 : Certificate start0_switch0_leaf
    (switchCell (428883/512000 : ℚ) (215227/256000 : ℚ)) := by
  exact switchCell_split (428883/512000 : ℚ) (859337/1024000 : ℚ) (215227/256000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_235 start0_switch0_node_236

theorem start0_switch0_node_238 : Certificate start0_switch0_leaf
    (switchCell (26707/32000 : ℚ) (215227/256000 : ℚ)) := by
  exact switchCell_split (26707/32000 : ℚ) (428883/512000 : ℚ) (215227/256000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_234 start0_switch0_node_237

theorem start0_switch0_node_239 : Certificate start0_switch0_leaf
    (switchCell (215227/256000 : ℚ) (862479/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_240 : Certificate start0_switch0_leaf
    (switchCell (862479/1024000 : ℚ) (17281/20480 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_241 : Certificate start0_switch0_leaf
    (switchCell (215227/256000 : ℚ) (17281/20480 : ℚ)) := by
  exact switchCell_split (215227/256000 : ℚ) (862479/1024000 : ℚ) (17281/20480 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_239 start0_switch0_node_240

theorem start0_switch0_node_242 : Certificate start0_switch0_leaf
    (switchCell (17281/20480 : ℚ) (865621/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_243 : Certificate start0_switch0_leaf
    (switchCell (865621/1024000 : ℚ) (108399/128000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_244 : Certificate start0_switch0_leaf
    (switchCell (17281/20480 : ℚ) (108399/128000 : ℚ)) := by
  exact switchCell_split (17281/20480 : ℚ) (865621/1024000 : ℚ) (108399/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_242 start0_switch0_node_243

theorem start0_switch0_node_245 : Certificate start0_switch0_leaf
    (switchCell (215227/256000 : ℚ) (108399/128000 : ℚ)) := by
  exact switchCell_split (215227/256000 : ℚ) (17281/20480 : ℚ) (108399/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_241 start0_switch0_node_244

theorem start0_switch0_node_246 : Certificate start0_switch0_leaf
    (switchCell (26707/32000 : ℚ) (108399/128000 : ℚ)) := by
  exact switchCell_split (26707/32000 : ℚ) (215227/256000 : ℚ) (108399/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_238 start0_switch0_node_245

theorem start0_switch0_node_247 : Certificate start0_switch0_leaf
    (switchCell (108399/128000 : ℚ) (868763/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_248 : Certificate start0_switch0_leaf
    (switchCell (868763/1024000 : ℚ) (435167/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_249 : Certificate start0_switch0_leaf
    (switchCell (108399/128000 : ℚ) (435167/512000 : ℚ)) := by
  exact switchCell_split (108399/128000 : ℚ) (868763/1024000 : ℚ) (435167/512000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_247 start0_switch0_node_248

theorem start0_switch0_node_250 : Certificate start0_switch0_leaf
    (switchCell (435167/512000 : ℚ) (174381/204800 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_251 : Certificate start0_switch0_leaf
    (switchCell (174381/204800 : ℚ) (218369/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_252 : Certificate start0_switch0_leaf
    (switchCell (435167/512000 : ℚ) (218369/256000 : ℚ)) := by
  exact switchCell_split (435167/512000 : ℚ) (174381/204800 : ℚ) (218369/256000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_250 start0_switch0_node_251

theorem start0_switch0_node_253 : Certificate start0_switch0_leaf
    (switchCell (108399/128000 : ℚ) (218369/256000 : ℚ)) := by
  exact switchCell_split (108399/128000 : ℚ) (435167/512000 : ℚ) (218369/256000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_249 start0_switch0_node_252

theorem start0_switch0_node_254 : Certificate start0_switch0_leaf
    (switchCell (218369/256000 : ℚ) (875047/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_255 : Certificate start0_switch0_leaf
    (switchCell (875047/1024000 : ℚ) (438309/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_256 : Certificate start0_switch0_leaf
    (switchCell (218369/256000 : ℚ) (438309/512000 : ℚ)) := by
  exact switchCell_split (218369/256000 : ℚ) (875047/1024000 : ℚ) (438309/512000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_254 start0_switch0_node_255

theorem start0_switch0_node_257 : Certificate start0_switch0_leaf
    (switchCell (438309/512000 : ℚ) (878189/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_258 : Certificate start0_switch0_leaf
    (switchCell (878189/1024000 : ℚ) (10997/12800 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_259 : Certificate start0_switch0_leaf
    (switchCell (438309/512000 : ℚ) (10997/12800 : ℚ)) := by
  exact switchCell_split (438309/512000 : ℚ) (878189/1024000 : ℚ) (10997/12800 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_257 start0_switch0_node_258

theorem start0_switch0_node_260 : Certificate start0_switch0_leaf
    (switchCell (218369/256000 : ℚ) (10997/12800 : ℚ)) := by
  exact switchCell_split (218369/256000 : ℚ) (438309/512000 : ℚ) (10997/12800 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_256 start0_switch0_node_259

theorem start0_switch0_node_261 : Certificate start0_switch0_leaf
    (switchCell (108399/128000 : ℚ) (10997/12800 : ℚ)) := by
  exact switchCell_split (108399/128000 : ℚ) (218369/256000 : ℚ) (10997/12800 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_253 start0_switch0_node_260

theorem start0_switch0_node_262 : Certificate start0_switch0_leaf
    (switchCell (26707/32000 : ℚ) (10997/12800 : ℚ)) := by
  exact switchCell_split (26707/32000 : ℚ) (108399/128000 : ℚ) (10997/12800 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_246 start0_switch0_node_261

theorem start0_switch0_node_263 : Certificate start0_switch0_leaf
    (switchCell (10997/12800 : ℚ) (881331/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_264 : Certificate start0_switch0_leaf
    (switchCell (881331/1024000 : ℚ) (441451/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_265 : Certificate start0_switch0_leaf
    (switchCell (10997/12800 : ℚ) (441451/512000 : ℚ)) := by
  exact switchCell_split (10997/12800 : ℚ) (881331/1024000 : ℚ) (441451/512000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_263 start0_switch0_node_264

theorem start0_switch0_node_266 : Certificate start0_switch0_leaf
    (switchCell (441451/512000 : ℚ) (884473/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_267 : Certificate start0_switch0_leaf
    (switchCell (884473/1024000 : ℚ) (221511/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_268 : Certificate start0_switch0_leaf
    (switchCell (441451/512000 : ℚ) (221511/256000 : ℚ)) := by
  exact switchCell_split (441451/512000 : ℚ) (884473/1024000 : ℚ) (221511/256000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_266 start0_switch0_node_267

theorem start0_switch0_node_269 : Certificate start0_switch0_leaf
    (switchCell (10997/12800 : ℚ) (221511/256000 : ℚ)) := by
  exact switchCell_split (10997/12800 : ℚ) (441451/512000 : ℚ) (221511/256000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_265 start0_switch0_node_268

theorem start0_switch0_node_270 : Certificate start0_switch0_leaf
    (switchCell (221511/256000 : ℚ) (177523/204800 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_271 : Certificate start0_switch0_leaf
    (switchCell (177523/204800 : ℚ) (444593/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_272 : Certificate start0_switch0_leaf
    (switchCell (221511/256000 : ℚ) (444593/512000 : ℚ)) := by
  exact switchCell_split (221511/256000 : ℚ) (177523/204800 : ℚ) (444593/512000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_270 start0_switch0_node_271

theorem start0_switch0_node_273 : Certificate start0_switch0_leaf
    (switchCell (444593/512000 : ℚ) (890757/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_274 : Certificate start0_switch0_leaf
    (switchCell (890757/1024000 : ℚ) (111541/128000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_275 : Certificate start0_switch0_leaf
    (switchCell (444593/512000 : ℚ) (111541/128000 : ℚ)) := by
  exact switchCell_split (444593/512000 : ℚ) (890757/1024000 : ℚ) (111541/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_273 start0_switch0_node_274

theorem start0_switch0_node_276 : Certificate start0_switch0_leaf
    (switchCell (221511/256000 : ℚ) (111541/128000 : ℚ)) := by
  exact switchCell_split (221511/256000 : ℚ) (444593/512000 : ℚ) (111541/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_272 start0_switch0_node_275

theorem start0_switch0_node_277 : Certificate start0_switch0_leaf
    (switchCell (10997/12800 : ℚ) (111541/128000 : ℚ)) := by
  exact switchCell_split (10997/12800 : ℚ) (221511/256000 : ℚ) (111541/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_269 start0_switch0_node_276

theorem start0_switch0_node_278 : Certificate start0_switch0_leaf
    (switchCell (111541/128000 : ℚ) (893899/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_279 : Certificate start0_switch0_leaf
    (switchCell (893899/1024000 : ℚ) (89547/102400 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_280 : Certificate start0_switch0_leaf
    (switchCell (111541/128000 : ℚ) (89547/102400 : ℚ)) := by
  exact switchCell_split (111541/128000 : ℚ) (893899/1024000 : ℚ) (89547/102400 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_278 start0_switch0_node_279

theorem start0_switch0_node_281 : Certificate start0_switch0_leaf
    (switchCell (89547/102400 : ℚ) (897041/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_282 : Certificate start0_switch0_leaf
    (switchCell (897041/1024000 : ℚ) (224653/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_283 : Certificate start0_switch0_leaf
    (switchCell (89547/102400 : ℚ) (224653/256000 : ℚ)) := by
  exact switchCell_split (89547/102400 : ℚ) (897041/1024000 : ℚ) (224653/256000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_281 start0_switch0_node_282

theorem start0_switch0_node_284 : Certificate start0_switch0_leaf
    (switchCell (111541/128000 : ℚ) (224653/256000 : ℚ)) := by
  exact switchCell_split (111541/128000 : ℚ) (89547/102400 : ℚ) (224653/256000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_280 start0_switch0_node_283

theorem start0_switch0_node_285 : Certificate start0_switch0_leaf
    (switchCell (224653/256000 : ℚ) (900183/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_286 : Certificate start0_switch0_leaf
    (switchCell (900183/1024000 : ℚ) (450877/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_287 : Certificate start0_switch0_leaf
    (switchCell (224653/256000 : ℚ) (450877/512000 : ℚ)) := by
  exact switchCell_split (224653/256000 : ℚ) (900183/1024000 : ℚ) (450877/512000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_285 start0_switch0_node_286

theorem start0_switch0_node_288 : Certificate start0_switch0_leaf
    (switchCell (450877/512000 : ℚ) (36133/40960 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_289 : Certificate start0_switch0_leaf
    (switchCell (36133/40960 : ℚ) (14139/16000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_290 : Certificate start0_switch0_leaf
    (switchCell (450877/512000 : ℚ) (14139/16000 : ℚ)) := by
  exact switchCell_split (450877/512000 : ℚ) (36133/40960 : ℚ) (14139/16000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_288 start0_switch0_node_289

theorem start0_switch0_node_291 : Certificate start0_switch0_leaf
    (switchCell (224653/256000 : ℚ) (14139/16000 : ℚ)) := by
  exact switchCell_split (224653/256000 : ℚ) (450877/512000 : ℚ) (14139/16000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_287 start0_switch0_node_290

theorem start0_switch0_node_292 : Certificate start0_switch0_leaf
    (switchCell (111541/128000 : ℚ) (14139/16000 : ℚ)) := by
  exact switchCell_split (111541/128000 : ℚ) (224653/256000 : ℚ) (14139/16000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_284 start0_switch0_node_291

theorem start0_switch0_node_293 : Certificate start0_switch0_leaf
    (switchCell (10997/12800 : ℚ) (14139/16000 : ℚ)) := by
  exact switchCell_split (10997/12800 : ℚ) (111541/128000 : ℚ) (14139/16000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_277 start0_switch0_node_292

theorem start0_switch0_node_294 : Certificate start0_switch0_leaf
    (switchCell (26707/32000 : ℚ) (14139/16000 : ℚ)) := by
  exact switchCell_split (26707/32000 : ℚ) (10997/12800 : ℚ) (14139/16000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_262 start0_switch0_node_293

theorem start0_switch0_node_295 : Certificate start0_switch0_leaf
    (switchCell (1571/2000 : ℚ) (14139/16000 : ℚ)) := by
  exact switchCell_split (1571/2000 : ℚ) (26707/32000 : ℚ) (14139/16000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_231 start0_switch0_node_294

theorem start0_switch0_node_296 : Certificate start0_switch0_leaf
    (switchCell (14139/16000 : ℚ) (906467/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_297 : Certificate start0_switch0_leaf
    (switchCell (906467/1024000 : ℚ) (454019/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_298 : Certificate start0_switch0_leaf
    (switchCell (14139/16000 : ℚ) (454019/512000 : ℚ)) := by
  exact switchCell_split (14139/16000 : ℚ) (906467/1024000 : ℚ) (454019/512000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_296 start0_switch0_node_297

theorem start0_switch0_node_299 : Certificate start0_switch0_leaf
    (switchCell (454019/512000 : ℚ) (909609/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_300 : Certificate start0_switch0_leaf
    (switchCell (909609/1024000 : ℚ) (45559/51200 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_301 : Certificate start0_switch0_leaf
    (switchCell (454019/512000 : ℚ) (45559/51200 : ℚ)) := by
  exact switchCell_split (454019/512000 : ℚ) (909609/1024000 : ℚ) (45559/51200 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_299 start0_switch0_node_300

theorem start0_switch0_node_302 : Certificate start0_switch0_leaf
    (switchCell (14139/16000 : ℚ) (45559/51200 : ℚ)) := by
  exact switchCell_split (14139/16000 : ℚ) (454019/512000 : ℚ) (45559/51200 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_298 start0_switch0_node_301

theorem start0_switch0_node_303 : Certificate start0_switch0_leaf
    (switchCell (45559/51200 : ℚ) (912751/1024000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_304 : Certificate start0_switch0_leaf
    (switchCell (912751/1024000 : ℚ) (457161/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_305 : Certificate start0_switch0_leaf
    (switchCell (45559/51200 : ℚ) (457161/512000 : ℚ)) := by
  exact switchCell_split (45559/51200 : ℚ) (912751/1024000 : ℚ) (457161/512000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_303 start0_switch0_node_304

theorem start0_switch0_node_306 : Certificate start0_switch0_leaf
    (switchCell (457161/512000 : ℚ) (114683/128000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_307 : Certificate start0_switch0_leaf
    (switchCell (45559/51200 : ℚ) (114683/128000 : ℚ)) := by
  exact switchCell_split (45559/51200 : ℚ) (457161/512000 : ℚ) (114683/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_305 start0_switch0_node_306

theorem start0_switch0_node_308 : Certificate start0_switch0_leaf
    (switchCell (14139/16000 : ℚ) (114683/128000 : ℚ)) := by
  exact switchCell_split (14139/16000 : ℚ) (45559/51200 : ℚ) (114683/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_302 start0_switch0_node_307

theorem start0_switch0_node_309 : Certificate start0_switch0_leaf
    (switchCell (114683/128000 : ℚ) (460303/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_310 : Certificate start0_switch0_leaf
    (switchCell (460303/512000 : ℚ) (230937/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_311 : Certificate start0_switch0_leaf
    (switchCell (114683/128000 : ℚ) (230937/256000 : ℚ)) := by
  exact switchCell_split (114683/128000 : ℚ) (460303/512000 : ℚ) (230937/256000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_309 start0_switch0_node_310

theorem start0_switch0_node_312 : Certificate start0_switch0_leaf
    (switchCell (230937/256000 : ℚ) (92689/102400 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_313 : Certificate start0_switch0_leaf
    (switchCell (92689/102400 : ℚ) (58127/64000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_314 : Certificate start0_switch0_leaf
    (switchCell (230937/256000 : ℚ) (58127/64000 : ℚ)) := by
  exact switchCell_split (230937/256000 : ℚ) (92689/102400 : ℚ) (58127/64000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_312 start0_switch0_node_313

theorem start0_switch0_node_315 : Certificate start0_switch0_leaf
    (switchCell (114683/128000 : ℚ) (58127/64000 : ℚ)) := by
  exact switchCell_split (114683/128000 : ℚ) (230937/256000 : ℚ) (58127/64000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_311 start0_switch0_node_314

theorem start0_switch0_node_316 : Certificate start0_switch0_leaf
    (switchCell (14139/16000 : ℚ) (58127/64000 : ℚ)) := by
  exact switchCell_split (14139/16000 : ℚ) (114683/128000 : ℚ) (58127/64000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_308 start0_switch0_node_315

theorem start0_switch0_node_317 : Certificate start0_switch0_leaf
    (switchCell (58127/64000 : ℚ) (466587/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_318 : Certificate start0_switch0_leaf
    (switchCell (466587/512000 : ℚ) (234079/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_319 : Certificate start0_switch0_leaf
    (switchCell (58127/64000 : ℚ) (234079/256000 : ℚ)) := by
  exact switchCell_split (58127/64000 : ℚ) (466587/512000 : ℚ) (234079/256000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_317 start0_switch0_node_318

theorem start0_switch0_node_320 : Certificate start0_switch0_leaf
    (switchCell (234079/256000 : ℚ) (469729/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_321 : Certificate start0_switch0_leaf
    (switchCell (469729/512000 : ℚ) (4713/5120 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_322 : Certificate start0_switch0_leaf
    (switchCell (234079/256000 : ℚ) (4713/5120 : ℚ)) := by
  exact switchCell_split (234079/256000 : ℚ) (469729/512000 : ℚ) (4713/5120 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_320 start0_switch0_node_321

theorem start0_switch0_node_323 : Certificate start0_switch0_leaf
    (switchCell (58127/64000 : ℚ) (4713/5120 : ℚ)) := by
  exact switchCell_split (58127/64000 : ℚ) (234079/256000 : ℚ) (4713/5120 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_319 start0_switch0_node_322

theorem start0_switch0_node_324 : Certificate start0_switch0_leaf
    (switchCell (4713/5120 : ℚ) (472871/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_325 : Certificate start0_switch0_leaf
    (switchCell (472871/512000 : ℚ) (237221/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_326 : Certificate start0_switch0_leaf
    (switchCell (4713/5120 : ℚ) (237221/256000 : ℚ)) := by
  exact switchCell_split (4713/5120 : ℚ) (472871/512000 : ℚ) (237221/256000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_324 start0_switch0_node_325

theorem start0_switch0_node_327 : Certificate start0_switch0_leaf
    (switchCell (237221/256000 : ℚ) (476013/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_328 : Certificate start0_switch0_leaf
    (switchCell (476013/512000 : ℚ) (29849/32000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_329 : Certificate start0_switch0_leaf
    (switchCell (237221/256000 : ℚ) (29849/32000 : ℚ)) := by
  exact switchCell_split (237221/256000 : ℚ) (476013/512000 : ℚ) (29849/32000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_327 start0_switch0_node_328

theorem start0_switch0_node_330 : Certificate start0_switch0_leaf
    (switchCell (4713/5120 : ℚ) (29849/32000 : ℚ)) := by
  exact switchCell_split (4713/5120 : ℚ) (237221/256000 : ℚ) (29849/32000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_326 start0_switch0_node_329

theorem start0_switch0_node_331 : Certificate start0_switch0_leaf
    (switchCell (58127/64000 : ℚ) (29849/32000 : ℚ)) := by
  exact switchCell_split (58127/64000 : ℚ) (4713/5120 : ℚ) (29849/32000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_323 start0_switch0_node_330

theorem start0_switch0_node_332 : Certificate start0_switch0_leaf
    (switchCell (14139/16000 : ℚ) (29849/32000 : ℚ)) := by
  exact switchCell_split (14139/16000 : ℚ) (58127/64000 : ℚ) (29849/32000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_316 start0_switch0_node_331

theorem start0_switch0_node_333 : Certificate start0_switch0_leaf
    (switchCell (29849/32000 : ℚ) (95831/102400 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_334 : Certificate start0_switch0_leaf
    (switchCell (95831/102400 : ℚ) (240363/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_335 : Certificate start0_switch0_leaf
    (switchCell (29849/32000 : ℚ) (240363/256000 : ℚ)) := by
  exact switchCell_split (29849/32000 : ℚ) (95831/102400 : ℚ) (240363/256000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_333 start0_switch0_node_334

theorem start0_switch0_node_336 : Certificate start0_switch0_leaf
    (switchCell (240363/256000 : ℚ) (482297/512000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_337 : Certificate start0_switch0_leaf
    (switchCell (482297/512000 : ℚ) (120967/128000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_338 : Certificate start0_switch0_leaf
    (switchCell (240363/256000 : ℚ) (120967/128000 : ℚ)) := by
  exact switchCell_split (240363/256000 : ℚ) (482297/512000 : ℚ) (120967/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_336 start0_switch0_node_337

theorem start0_switch0_node_339 : Certificate start0_switch0_leaf
    (switchCell (29849/32000 : ℚ) (120967/128000 : ℚ)) := by
  exact switchCell_split (29849/32000 : ℚ) (240363/256000 : ℚ) (120967/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_335 start0_switch0_node_338

theorem start0_switch0_node_340 : Certificate start0_switch0_leaf
    (switchCell (120967/128000 : ℚ) (48701/51200 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_341 : Certificate start0_switch0_leaf
    (switchCell (48701/51200 : ℚ) (61269/64000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_342 : Certificate start0_switch0_leaf
    (switchCell (120967/128000 : ℚ) (61269/64000 : ℚ)) := by
  exact switchCell_split (120967/128000 : ℚ) (48701/51200 : ℚ) (61269/64000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_340 start0_switch0_node_341

theorem start0_switch0_node_343 : Certificate start0_switch0_leaf
    (switchCell (29849/32000 : ℚ) (61269/64000 : ℚ)) := by
  exact switchCell_split (29849/32000 : ℚ) (120967/128000 : ℚ) (61269/64000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_339 start0_switch0_node_342

theorem start0_switch0_node_344 : Certificate start0_switch0_leaf
    (switchCell (61269/64000 : ℚ) (246647/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_345 : Certificate start0_switch0_leaf
    (switchCell (246647/256000 : ℚ) (124109/128000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_346 : Certificate start0_switch0_leaf
    (switchCell (61269/64000 : ℚ) (124109/128000 : ℚ)) := by
  exact switchCell_split (61269/64000 : ℚ) (246647/256000 : ℚ) (124109/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_344 start0_switch0_node_345

theorem start0_switch0_node_347 : Certificate start0_switch0_leaf
    (switchCell (124109/128000 : ℚ) (249789/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_348 : Certificate start0_switch0_leaf
    (switchCell (249789/256000 : ℚ) (1571/1600 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_349 : Certificate start0_switch0_leaf
    (switchCell (124109/128000 : ℚ) (1571/1600 : ℚ)) := by
  exact switchCell_split (124109/128000 : ℚ) (249789/256000 : ℚ) (1571/1600 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_347 start0_switch0_node_348

theorem start0_switch0_node_350 : Certificate start0_switch0_leaf
    (switchCell (61269/64000 : ℚ) (1571/1600 : ℚ)) := by
  exact switchCell_split (61269/64000 : ℚ) (124109/128000 : ℚ) (1571/1600 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_346 start0_switch0_node_349

theorem start0_switch0_node_351 : Certificate start0_switch0_leaf
    (switchCell (29849/32000 : ℚ) (1571/1600 : ℚ)) := by
  exact switchCell_split (29849/32000 : ℚ) (61269/64000 : ℚ) (1571/1600 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_343 start0_switch0_node_350

theorem start0_switch0_node_352 : Certificate start0_switch0_leaf
    (switchCell (14139/16000 : ℚ) (1571/1600 : ℚ)) := by
  exact switchCell_split (14139/16000 : ℚ) (29849/32000 : ℚ) (1571/1600 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_332 start0_switch0_node_351

theorem start0_switch0_node_353 : Certificate start0_switch0_leaf
    (switchCell (1571/2000 : ℚ) (1571/1600 : ℚ)) := by
  exact switchCell_split (1571/2000 : ℚ) (14139/16000 : ℚ) (1571/1600 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_295 start0_switch0_node_352

theorem start0_switch0_node_354 : Certificate start0_switch0_leaf
    (switchCell (1571/1600 : ℚ) (252931/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_355 : Certificate start0_switch0_leaf
    (switchCell (252931/256000 : ℚ) (127251/128000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_356 : Certificate start0_switch0_leaf
    (switchCell (1571/1600 : ℚ) (127251/128000 : ℚ)) := by
  exact switchCell_split (1571/1600 : ℚ) (252931/256000 : ℚ) (127251/128000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_354 start0_switch0_node_355

theorem start0_switch0_node_357 : Certificate start0_switch0_leaf
    (switchCell (127251/128000 : ℚ) (256073/256000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_358 : Certificate start0_switch0_leaf
    (switchCell (256073/256000 : ℚ) (64411/64000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_359 : Certificate start0_switch0_leaf
    (switchCell (127251/128000 : ℚ) (64411/64000 : ℚ)) := by
  exact switchCell_split (127251/128000 : ℚ) (256073/256000 : ℚ) (64411/64000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_357 start0_switch0_node_358

theorem start0_switch0_node_360 : Certificate start0_switch0_leaf
    (switchCell (1571/1600 : ℚ) (64411/64000 : ℚ)) := by
  exact switchCell_split (1571/1600 : ℚ) (127251/128000 : ℚ) (64411/64000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_356 start0_switch0_node_359

theorem start0_switch0_node_361 : Certificate start0_switch0_leaf
    (switchCell (64411/64000 : ℚ) (130393/128000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_362 : Certificate start0_switch0_leaf
    (switchCell (130393/128000 : ℚ) (32991/32000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_363 : Certificate start0_switch0_leaf
    (switchCell (64411/64000 : ℚ) (32991/32000 : ℚ)) := by
  exact switchCell_split (64411/64000 : ℚ) (130393/128000 : ℚ) (32991/32000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_361 start0_switch0_node_362

theorem start0_switch0_node_364 : Certificate start0_switch0_leaf
    (switchCell (1571/1600 : ℚ) (32991/32000 : ℚ)) := by
  exact switchCell_split (1571/1600 : ℚ) (64411/64000 : ℚ) (32991/32000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_360 start0_switch0_node_363

theorem start0_switch0_node_365 : Certificate start0_switch0_leaf
    (switchCell (32991/32000 : ℚ) (26707/25600 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_366 : Certificate start0_switch0_leaf
    (switchCell (26707/25600 : ℚ) (67553/64000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_367 : Certificate start0_switch0_leaf
    (switchCell (32991/32000 : ℚ) (67553/64000 : ℚ)) := by
  exact switchCell_split (32991/32000 : ℚ) (26707/25600 : ℚ) (67553/64000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_365 start0_switch0_node_366

theorem start0_switch0_node_368 : Certificate start0_switch0_leaf
    (switchCell (67553/64000 : ℚ) (136677/128000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_369 : Certificate start0_switch0_leaf
    (switchCell (136677/128000 : ℚ) (17281/16000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_370 : Certificate start0_switch0_leaf
    (switchCell (67553/64000 : ℚ) (17281/16000 : ℚ)) := by
  exact switchCell_split (67553/64000 : ℚ) (136677/128000 : ℚ) (17281/16000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_368 start0_switch0_node_369

theorem start0_switch0_node_371 : Certificate start0_switch0_leaf
    (switchCell (32991/32000 : ℚ) (17281/16000 : ℚ)) := by
  exact switchCell_split (32991/32000 : ℚ) (67553/64000 : ℚ) (17281/16000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_367 start0_switch0_node_370

theorem start0_switch0_node_372 : Certificate start0_switch0_leaf
    (switchCell (1571/1600 : ℚ) (17281/16000 : ℚ)) := by
  exact switchCell_split (1571/1600 : ℚ) (32991/32000 : ℚ) (17281/16000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_364 start0_switch0_node_371

theorem start0_switch0_node_373 : Certificate start0_switch0_leaf
    (switchCell (17281/16000 : ℚ) (14139/12800 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_374 : Certificate start0_switch0_leaf
    (switchCell (14139/12800 : ℚ) (36133/32000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_375 : Certificate start0_switch0_leaf
    (switchCell (17281/16000 : ℚ) (36133/32000 : ℚ)) := by
  exact switchCell_split (17281/16000 : ℚ) (14139/12800 : ℚ) (36133/32000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_373 start0_switch0_node_374

theorem start0_switch0_node_376 : Certificate start0_switch0_leaf
    (switchCell (36133/32000 : ℚ) (73837/64000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_377 : Certificate start0_switch0_leaf
    (switchCell (73837/64000 : ℚ) (4713/4000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_378 : Certificate start0_switch0_leaf
    (switchCell (36133/32000 : ℚ) (4713/4000 : ℚ)) := by
  exact switchCell_split (36133/32000 : ℚ) (73837/64000 : ℚ) (4713/4000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_376 start0_switch0_node_377

theorem start0_switch0_node_379 : Certificate start0_switch0_leaf
    (switchCell (17281/16000 : ℚ) (4713/4000 : ℚ)) := by
  exact switchCell_split (17281/16000 : ℚ) (36133/32000 : ℚ) (4713/4000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_375 start0_switch0_node_378

theorem start0_switch0_node_380 : Certificate start0_switch0_leaf
    (switchCell (1571/1600 : ℚ) (4713/4000 : ℚ)) := by
  exact switchCell_split (1571/1600 : ℚ) (17281/16000 : ℚ) (4713/4000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_372 start0_switch0_node_379

theorem start0_switch0_node_381 : Certificate start0_switch0_leaf
    (switchCell (1571/2000 : ℚ) (4713/4000 : ℚ)) := by
  exact switchCell_split (1571/2000 : ℚ) (1571/1600 : ℚ) (4713/4000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_353 start0_switch0_node_380

theorem start0_switch0_node_382 : Certificate start0_switch0_leaf
    (switchCell (4713/4000 : ℚ) (1571/1280 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_383 : Certificate start0_switch0_leaf
    (switchCell (1571/1280 : ℚ) (20423/16000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_384 : Certificate start0_switch0_leaf
    (switchCell (4713/4000 : ℚ) (20423/16000 : ℚ)) := by
  exact switchCell_split (4713/4000 : ℚ) (1571/1280 : ℚ) (20423/16000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_382 start0_switch0_node_383

theorem start0_switch0_node_385 : Certificate start0_switch0_leaf
    (switchCell (20423/16000 : ℚ) (10997/8000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_386 : Certificate start0_switch0_leaf
    (switchCell (4713/4000 : ℚ) (10997/8000 : ℚ)) := by
  exact switchCell_split (4713/4000 : ℚ) (20423/16000 : ℚ) (10997/8000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_384 start0_switch0_node_385

theorem start0_switch0_node_387 : Certificate start0_switch0_leaf
    (switchCell (10997/8000 : ℚ) (1571/1000 : ℚ)) := by
  apply Certificate.accept
  norm_num [start0_switch0_leaf,start0_switch0_p,start0_switch0_q,start0_switch0_b,start0_switch0_d2,start0_switch0_d1,start0_switch0_bound,switchCell,switchDirectUpperQ,switchQuadraticCell,switchLinearCell,RatInterval.ofRat,RatInterval.mul,RatInterval.add,RationalTrigCellBounds.sinCell,RationalTrigCellBounds.squareCell,RationalTrigCellBounds.midpoint,RationalTrigCellBounds.halfWidth,sinLoNLag,sinHiNLag,sinTQ,CompactQuadraticMomentMaximum.maximumQ,Finset.sum_range_succ]

theorem start0_switch0_node_388 : Certificate start0_switch0_leaf
    (switchCell (4713/4000 : ℚ) (1571/1000 : ℚ)) := by
  exact switchCell_split (4713/4000 : ℚ) (10997/8000 : ℚ) (1571/1000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_386 start0_switch0_node_387

theorem start0_switch0_node_389 : Certificate start0_switch0_leaf
    (switchCell (1571/2000 : ℚ) (1571/1000 : ℚ)) := by
  exact switchCell_split (1571/2000 : ℚ) (4713/4000 : ℚ) (1571/1000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_381 start0_switch0_node_388

theorem start0_switch0_node_390 : Certificate start0_switch0_leaf
    (switchCell (0 : ℚ) (1571/1000 : ℚ)) := by
  exact switchCell_split (0 : ℚ) (1571/2000 : ℚ) (1571/1000 : ℚ)
    (by norm_num) (by norm_num) start0_switch0_node_168 start0_switch0_node_389

theorem start0_switch0_full_angle_upper :
    ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi/2), ∀ y ∈ Set.Icc (0 : ℝ) 1,
      switchObjective start0_switch0_p start0_switch0_q start0_switch0_b start0_switch0_d2 start0_switch0_d1 t y ≤ (start0_switch0_bound : ℝ) := by
  intro t ht y hy
  have hdom : RatInterval.piHi/2 ≤ (1571/1000 : ℚ) := by norm_num [RatInterval.piHi]
  have hp : Real.pi/2 ≤ ((1571/1000 : ℚ) : ℝ) :=
    RatInterval.pi_div_two_lt_hi.le.trans (by exact_mod_cast hdom)
  have htcell : (switchCell 0 (1571/1000 : ℚ) 0).Mem t :=
    ⟨by simpa [switchCell] using ht.1,by simpa [switchCell] using ht.2.trans hp⟩
  apply certificate_sound start0_switch0_node_390
    (fun a => ∀ y ∈ Set.Icc (0 : ℝ) 1,
      switchObjective start0_switch0_p start0_switch0_q start0_switch0_b start0_switch0_d2 start0_switch0_d1 (a 0) y ≤ (start0_switch0_bound : ℝ))
    (by intro B hb a ha yy hyy;
        exact switch_upper_of_direct_certificate _ _ _ _ _ B _ hb (a 0) (ha 0) yy hyy)
    (fun _ => t) (by intro i; fin_cases i; exact htcell) y hy

#print axioms start0_switch0_full_angle_upper
#print axioms start0_switch0_node_390
end N11Formalization.SharedMomentConcreteLeafControls
