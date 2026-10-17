import N11Formalization.ActualTriangleBoundaryChain

/-! Exact signed-edge control for the exploratory13-face abstract family.
It is NOT an actual geometric refinement. Its six displayed interior rows
force face0's orientation coefficient to vanish, so it cannot have all
nonzero positive/negative face orientations. No MILP output is trusted. -/
set_option autoImplicit false
namespace N11Formalization.ProbeA13OrientationControls
open ActualTriangleBoundaryChain

def toyLabels : Fin 13 → Fin 3 → Fin 11 :=
  ![![0,1,10],![0,7,8],![0,7,10],![1,2,9],![1,3,9],![1,3,10],
    ![2,3,10],![2,9,10],![3,4,9],![4,5,9],![5,6,9],![6,7,9],![7,9,10]]

def toyTotal (s : Fin 13 → ℤ) (i j : Fin 11) : ℤ :=
  ∑ a : Fin 13, s a * triangleBoundary (toyLabels a) i j

theorem toy_signed_rows (s : Fin 13 → ℤ) :
    toyTotal s 1 10 = s 0-s 5 ∧
    toyTotal s 1 3 = s 4+s 5 ∧
    toyTotal s 1 9 = -s 3-s 4 ∧
    toyTotal s 2 9 = s 3+s 7 ∧
    toyTotal s 2 10 = -s 6-s 7 ∧
    toyTotal s 3 10 = s 5+s 6 := by
  norm_num [toyTotal,toyLabels,triangleBoundary,Fin.sum_univ_succ,
    Matrix.cons_val_two,Fin.ext_iff,Fin.succ] <;> (repeat constructor) <;> ring

theorem toy_orientation_rows_force_zero (s : Fin 13 → ℤ)
    (h110 : toyTotal s 1 10 = 0) (h13 : toyTotal s 1 3 = 0)
    (h19 : toyTotal s 1 9 = 0) (h29 : toyTotal s 2 9 = 0)
    (h210 : toyTotal s 2 10 = 0) (h310 : toyTotal s 3 10 = 0) :
    s 0 = 0 := by
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := toy_signed_rows s
  omega

theorem toy_no_nonzero_orientations (s : Fin 13 → ℤ)
    (hn : s 0 = 1 ∨ s 0 = -1)
    (h110 : toyTotal s 1 10 = 0) (h13 : toyTotal s 1 3 = 0)
    (h19 : toyTotal s 1 9 = 0) (h29 : toyTotal s 2 9 = 0)
    (h210 : toyTotal s 2 10 = 0) (h310 : toyTotal s 3 10 = 0) : False := by
  have hh := toy_orientation_rows_force_zero s h110 h13 h19 h29 h210 h310
  omega

end N11Formalization.ProbeA13OrientationControls
#check @N11Formalization.ProbeA13OrientationControls.toy_no_nonzero_orientations
#print axioms N11Formalization.ProbeA13OrientationControls.toy_signed_rows
#print axioms N11Formalization.ProbeA13OrientationControls.toy_no_nonzero_orientations
