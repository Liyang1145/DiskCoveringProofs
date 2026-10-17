import N11Formalization.SourceActualContraction
import N11Formalization.SourceActiveMatrixIntervals

/-! Rational proposed centres for all9 columns of the ACTUAL20-node solve.
Only integer residual checks appear here. No rational centre is asserted equal
to actual H20; real residual semantics and solution enclosures are separate. -/
set_option autoImplicit false
namespace N11Formalization.SourceH20ResidualProposal
open N11Formalization ResumeLocalIncidence HarmonicSourceTransport
open SourceActiveLaplacian SourceActiveFiniteSystem SourceContractionProposal
open SourceCompactStressIntervals
section

def YN : Fin 20 → Fin 9 → ℤ :=
 ![![1790654,158811,158811,1790654,1936446,5550329,37071918,49605938,1936446],
   ![7649042,428703,327362,2967494,3130432,2353718,1143003,42949958,39050290],
   ![45043598,1822672,941019,4314763,3981648,2729333,1305719,5742106,34119147],
   ![47991764,44612041,1558423,1683625,985988,380987,158179,495682,2133310],
   ![1637308,47721318,47721318,1637308,461730,150445,58410,150445,461730],
   ![1683625,1558423,44612041,47991764,2133310,495682,158179,380987,985988],
   ![4314763,941019,1822672,45043598,34119147,5742106,1305719,2729333,3981648],
   ![2967494,327362,428703,7649042,39050290,42949958,1143003,2353718,3130432],
   ![1790654,158811,158811,1790654,1936446,49605938,37071918,5550329,1936446],
   ![21919076,11118883,11118883,21919076,12140540,4032196,1578612,4032196,12140540],
   ![15642728,1387333,1387333,15642728,16916327,12911449,6284330,12911449,16916327],
   ![30503881,3891301,3490253,11977048,9900921,6175798,2904603,7546256,23609942],
   ![11977048,3490253,3891301,30503881,23609942,7546256,2904603,6175798,9900921],
   ![23422390,1312746,1002427,9086863,9585801,7207400,3500029,17358552,27523797],
   ![36135289,16938331,5364158,10995067,6611797,2658839,1118974,3650084,16527465],
   ![25488431,34285369,18459278,8466011,4576796,1538885,605647,1581046,4998541],
   ![8466011,18459278,34285369,25488431,4998541,1581046,605647,1538885,4576796],
   ![10995067,5364158,16938331,36135289,16527465,3650084,1118974,2658839,6611797],
   ![9086863,1002427,1312746,23422390,27523797,17358552,3500029,7207400,9585801],
   ![7087814,628609,628609,7087814,7664890,21969459,25298462,21969459,7664890]]

def anchorN : SourceEdge → Fin 9 → ℤ
  | .inl (k,_), j => if j=siteMap k then -1 else 0
  | .inr _, _ => 0

def coefficientN (e : SourceEdge) (j : Fin 9) : ℤ :=
  anchorN e j*100000000+
    ∑ k : Fin 20,incidenceZ e (nodeEquiv.symm k)*YN k j

def projectionN (i : Fin 20) (e : SourceEdge) : ℤ :=
  ∑ k : Fin 20,CN i k*incidenceZ e (nodeEquiv.symm k)

def multiplierN (i : Fin 20) (j : Fin 9) (e : SourceEdge) : ℤ :=
  projectionN i e*coefficientN e j

def EL (i : Fin 20) (j : Fin 9) : ℤ :=
  -(∑ e : SourceEdge,
    if 0 ≤ multiplierN i j e then hiN (srcFlat e)*multiplierN i j e
    else loN (srcFlat e)*multiplierN i j e)

def EH (i : Fin 20) (j : Fin 9) : ℤ :=
  -(∑ e : SourceEdge,
    if 0 ≤ multiplierN i j e then loN (srcFlat e)*multiplierN i j e
    else hiN (srcFlat e)*multiplierN i j e)

def columnCheck (j : Fin 9) : Prop :=
  ∀ i : Fin 20,max |EL i j| |EH i j| ≤ 3000000000000000000000

private theorem col0 : columnCheck 0 := by
  intro i
  fin_cases i <;> unfold EL EH <;> decide +kernel
private theorem col1 : columnCheck 1 := by
  intro i
  fin_cases i <;> unfold EL EH <;> decide +kernel
private theorem col2 : columnCheck 2 := by
  intro i
  fin_cases i <;> unfold EL EH <;> decide +kernel
private theorem col3 : columnCheck 3 := by
  intro i
  fin_cases i <;> unfold EL EH <;> decide +kernel
private theorem col4 : columnCheck 4 := by
  intro i
  fin_cases i <;> unfold EL EH <;> decide +kernel
private theorem col5 : columnCheck 5 := by
  intro i
  fin_cases i <;> unfold EL EH <;> decide +kernel
private theorem col6 : columnCheck 6 := by
  intro i
  fin_cases i <;> unfold EL EH <;> decide +kernel
private theorem col7 : columnCheck 7 := by
  intro i
  fin_cases i <;> unfold EL EH <;> decide +kernel
private theorem col8 : columnCheck 8 := by
  intro i
  fin_cases i <;> unfold EL EH <;> decide +kernel

theorem all_columns (i : Fin 20) (j : Fin 9) :
    max |EL i j| |EH i j| ≤ 3000000000000000000000 := by
  fin_cases j
  · exact col0 i
  · exact col1 i
  · exact col2 i
  · exact col3 i
  · exact col4 i
  · exact col5 i
  · exact col6 i
  · exact col7 i
  · exact col8 i

end
end N11Formalization.SourceH20ResidualProposal
#check @N11Formalization.SourceH20ResidualProposal.all_columns
#print axioms N11Formalization.SourceH20ResidualProposal.all_columns
