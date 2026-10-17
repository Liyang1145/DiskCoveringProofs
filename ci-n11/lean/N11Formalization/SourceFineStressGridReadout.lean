import N11Formalization.SourceFineStressIntervals
import N11Formalization.SourceStressGridReadout

/-! Staged kernel endpoint equalities for SAME fine source expressions.
Host rational proposals supply literals only; every equality is kernel checked.
No interval midpoint is identified with the true source value. -/
set_option autoImplicit false
namespace N11Formalization.SourceFineStressGridReadout
open N11Formalization RatInterval SourceRefinedBoundaryIntervals

macro "fine_geometry_eval" : tactic =>
  `(tactic| (simp only [ringBox,pinBox,wBox,fine]; nd_eval))

theorem ring00 : ringBox 0 0=intv (-76470619/100000000) (-76470616/100000000) := by fine_geometry_eval
theorem ring01 : ringBox 0 1=intv (-29836983/100000000) (-29836979/100000000) := by fine_geometry_eval
theorem ring10 : ringBox 1 0=intv (-35578741/100000000) (-35578738/100000000) := by fine_geometry_eval
theorem ring11 : ringBox 1 1=intv (-67361113/100000000) (-67361110/100000000) := by fine_geometry_eval
theorem ring20 : ringBox 2 0=intv (9483654/100000000) (9483657/100000000) := by fine_geometry_eval
theorem ring21 : ringBox 2 1=intv (-69442413/100000000) (-69442411/100000000) := by fine_geometry_eval
theorem ring30 : ringBox 3 0=intv (61581165/100000000) (61581169/100000000) := by fine_geometry_eval
theorem ring31 : ringBox 3 1=intv (-59860858/100000000) (-59860855/100000000) := by fine_geometry_eval
theorem ring40 : ringBox 4 0=intv (89252163/100000000) (89252183/100000000) := by fine_geometry_eval
theorem ring41 : ringBox 4 1=intv 0 0 := by fine_geometry_eval
theorem ring50 : ringBox 5 0=intv (61581165/100000000) (61581169/100000000) := by fine_geometry_eval
theorem ring51 : ringBox 5 1=intv (59860855/100000000) (59860858/100000000) := by fine_geometry_eval
theorem ring60 : ringBox 6 0=intv (9483654/100000000) (9483657/100000000) := by fine_geometry_eval
theorem ring61 : ringBox 6 1=intv (69442411/100000000) (69442413/100000000) := by fine_geometry_eval
theorem ring70 : ringBox 7 0=intv (-35578741/100000000) (-35578738/100000000) := by fine_geometry_eval
theorem ring71 : ringBox 7 1=intv (67361110/100000000) (67361113/100000000) := by fine_geometry_eval
theorem ring80 : ringBox 8 0=intv (-76470619/100000000) (-76470616/100000000) := by fine_geometry_eval
theorem ring81 : ringBox 8 1=intv (29836979/100000000) (29836983/100000000) := by fine_geometry_eval
theorem pin10 : pinBox 1 0=intv (-11636647/100000000) (-11636639/100000000) := by fine_geometry_eval
theorem pin11 : pinBox 1 1=intv (-37854279/100000000) (-37854275/100000000) := by fine_geometry_eval
theorem pin20 : pinBox 2 0=intv (30603950/100000000) (30603957/100000000) := by fine_geometry_eval
theorem pin21 : pinBox 2 1=intv (-37854280/100000000) (-37854274/100000000) := by fine_geometry_eval
theorem pin30 : pinBox 3 0=intv (58274948/100000000) (58274972/100000000) := by fine_geometry_eval
theorem pin31 : pinBox 3 1=intv (-22006582/100000000) (-22006577/100000000) := by fine_geometry_eval
theorem pin80 : pinBox 8 0=intv (-52941238/100000000) (-52941233/100000000) := by fine_geometry_eval
theorem pin81 : pinBox 8 1=intv (-5/100000000) (5/100000000) := by fine_geometry_eval
theorem w0 : wBox 0=intv (6177448/100000000) (6177449/100000000) := by fine_geometry_eval
theorem w1 : wBox 1=intv (31588135/100000000) (31588136/100000000) := by fine_geometry_eval

theorem sine4 : fine (sinTotLag (ndAngleBox ndBox 4))=
    intv (37854276/100000000) (37854278/100000000) := by
  unfold fine
  nd_eval
theorem rho4 : fine (ndRhoBox ndBox 4)=
    intv (89252163/100000000) (89252183/100000000) := by
  unfold fine
  nd_eval
theorem den4 : slopeDen=intv (3306197/100000000) (3306217/100000000) := by
  unfold slopeDen fine
  nd_eval
theorem velocitySlope4 : slopeBox=
    intv (1021885741/100000000) (1021892207/100000000) := by
  unfold slopeBox
  rw [sine4,rho4]
  unfold div inv
  rw [den4]
  norm_num [fine,mul,intv]

theorem slope0_eq : SourceFineStressIntervals.slopeI 0=
    intv (29836980/100000000) (29836982/100000000) := by
  unfold SourceFineStressIntervals.slopeI fine
  nd_eval
theorem slope1_eq : SourceFineStressIntervals.slopeI 1=
    intv (25465527/100000000) (25465529/100000000) := by
  unfold SourceFineStressIntervals.slopeI fine
  nd_eval
theorem slope2_eq : SourceFineStressIntervals.slopeI 2=
    intv (19424295/100000000) (19424297/100000000) := by
  unfold SourceFineStressIntervals.slopeI fine
  nd_eval
theorem slope3_eq : SourceFineStressIntervals.slopeI 3=
    intv (32095133/100000000) (32095135/100000000) := by
  unfold SourceFineStressIntervals.slopeI fine
  nd_eval
theorem slope4_eq : SourceFineStressIntervals.slopeI 4=
    intv (33785760/100000000) (33785770/100000000) := by
  unfold SourceFineStressIntervals.slopeI fine
  nd_eval

macro "fine_numerator_eval" : tactic =>
  `(tactic|
    (simp only [numeratorBox,fanBox,centralBox,
      SourceBoundaryMultiplierIntervals.innerBox,normalPBox,normalQBox,normalCBox,
      SourceBoundarySignBounds.contact,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk]
     simp only [nd_fin_succ_1,nd_fin_succ_2,nd_fin_succ_3,nd_fin_succ_8]
     simp [velocityBox,SourceBoundaryMultiplierIntervals.widthQ,
      SourceBoundaryMultiplierIntervals.directionQ,Fin.ext_iff,
      ring00,ring01,ring10,ring11,ring20,ring21,ring30,ring31,ring40,ring41,
      ring50,ring51,ring60,ring61,ring70,ring71,ring80,ring81,
      pin10,pin11,pin20,pin21,pin30,pin31,pin80,pin81,w0,w1,velocitySlope4,
      SourceRefinedFanCoefficientBounds.ABox,SourceRefinedFanCoefficientBounds.BBox]
     nd_eval))

theorem num0_eq : numeratorBox 0=intv
    (-80664118082237080354177312967412710618312155941/4835703278458516698824704000000000000000000000000)
    (-322634600668625999910622836299656827270431229/19342813113834066795298816000000000000000000000) := by
  fine_numerator_eval
theorem num1_eq : numeratorBox 1=intv
    (-65050002198677412297010653008737307913707584437/4835703278458516698824704000000000000000000000000)
    (-6504518568945411898105184806680057053053907497/483570327845851669882470400000000000000000000000) := by
  fine_numerator_eval
theorem num2_eq : numeratorBox 2=intv
    (-93471248604273846562390827076420176408989779983/4835703278458516698824704000000000000000000000000)
    (-23367052166411738227777463010023503012578101491/1208925819614629174706176000000000000000000000000) := by
  fine_numerator_eval
theorem num3_eq : numeratorBox 3=intv
    (-17967919598112592502317553314446399171514910769/967140655691703339764940800000000000000000000000)
    (-17967368082226501445028458644908781040251835113/967140655691703339764940800000000000000000000000) := by
  fine_numerator_eval
theorem num4_eq : numeratorBox 4=intv
    (-56178811456227129493838199088445338184657213181/9671406556917033397649408000000000000000000000000)
    (-1123454229043452556756670129417011776951531021/193428131138340667952988160000000000000000000000) := by
  fine_numerator_eval

end N11Formalization.SourceFineStressGridReadout
#check @N11Formalization.SourceFineStressGridReadout.num4_eq
#print axioms N11Formalization.SourceFineStressGridReadout.num4_eq
