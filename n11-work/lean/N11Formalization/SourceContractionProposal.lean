import N11Formalization.SourceCompactStressIntervals
import N11Formalization.SourceActiveFiniteSystem

/-! Exact rational preconditioner PROPOSAL and integer finite checks.
No statement that this proposal equals the inverse is made. The matrix
endpoint tables are bound to actual integer incidence and certified stress
endpoints. Semantic real-matrix contraction is a separate consumer. -/
set_option autoImplicit false
namespace N11Formalization.SourceContractionProposal
open N11Formalization ResumeLocalIncidence HarmonicSourceTransport
open SourceCompactStressIntervals SourceActiveLaplacian SourceActiveFiniteSystem
section

def CN : Fin 20 → Fin 20 → ℤ :=
 ![![1740367065,29360482,33540174,4063156,1500373,4063156,33540174,29360482,164175823,40550036,161426446,74610939,74610939,89905716,28743234,15557343,15557343,28743234,89905716,649845059],
   ![29360482,1286460350,146714301,11668232,3313426,8165906,54716290,46813904,29360482,88517586,256486171,166751856,124903573,453325943,86926536,35000578,33713157,56657877,143350428,116215430],
   ![33540174,146714301,873646737,52721985,10810002,22252223,73276557,54716290,33540174,283169384,292998971,554796297,190721923,449258786,411102584,117688943,106488556,147769369,167548589,132759599],
   ![4063156,11668232,52721985,1507085808,36526810,19159173,22252223,8165906,4063156,260225316,35494761,96582176,82722015,35729686,521075457,652219616,105272277,121073784,25005095,16082890],
   ![1500373,3313426,10810002,36526810,1697632811,36526810,10810002,3313426,1500373,130573068,13106899,39896290,39896290,10146154,67697022,560725923,560725923,67697022,10146154,5938815],
   ![4063156,8165906,22252223,19159173,36526810,1507085808,52721985,11668232,4063156,260225316,35494761,82722015,96582176,25005095,121073784,105272277,652219616,521075457,35729686,16082890],
   ![33540174,54716290,73276557,22252223,10810002,52721985,873646737,146714301,33540174,283169384,292998971,190721923,554796297,167548589,147769369,106488556,117688943,411102584,449258786,132759599],
   ![29360482,46813904,54716290,8165906,3313426,11668232,146714301,1286460350,29360482,88517586,256486171,124903573,166751856,143350428,56657877,33713157,35000578,86926536,453325943,116215430],
   ![164175823,29360482,33540174,4063156,1500373,4063156,33540174,29360482,1740367065,40550036,161426446,74610939,74610939,89905716,28743234,15557343,15557343,28743234,89905716,649845059],
   ![40550036,88517586,283169384,260225316,130573068,260225316,283169384,88517586,40550036,3631154930,354235448,1098391549,1098391549,271052672,1678861696,1353910179,1353910179,1678861696,271052672,160506216],
   ![161426446,256486171,292998971,35494761,13106899,35494761,292998971,256486171,161426446,354235448,1410182966,651783381,651783381,785394913,251094047,135905241,135905241,251094047,785394913,638962400],
   ![74610939,166751856,554796297,96582176,39896290,82722015,190721923,124903573,74610939,1098391549,651783381,4158177167,547880688,510616456,662195964,416231457,411136597,542410298,382471423,295326978],
   ![74610939,124903573,190721923,82722015,39896290,96582176,554796297,166751856,74610939,1098391549,651783381,547880688,4158177167,382471423,542410298,411136597,416231457,662195964,510616456,295326978],
   ![89905716,453325943,449258786,35729686,10146154,25005095,167548589,143350428,89905716,271052672,785394913,510616456,382471423,1388144585,266180664,107176446,103234191,173493988,438958157,355867168],
   ![28743234,86926536,411102584,521075457,67697022,121073784,147769369,56657877,28743234,1678861696,251094047,662195964,542410298,266180664,4238785991,775467759,628431040,781793879,173493988,113772226],
   ![15557343,35000578,117688943,652219616,560725923,105272277,106488556,33713157,15557343,1353910179,135905241,416231457,411136597,107176446,775467759,10968619004,659698296,628431040,103234191,61579484],
   ![15557343,33713157,106488556,105272277,560725923,652219616,117688943,35000578,15557343,1353910179,135905241,411136597,416231457,103234191,628431040,659698296,10968619004,775467759,107176446,61579484],
   ![28743234,56657877,147769369,121073784,67697022,521075457,411102584,86926536,28743234,1678861696,251094047,542410298,662195964,173493988,781793879,628431040,775467759,4238785991,266180664,113772226],
   ![89905716,143350428,167548589,25005095,10146154,35729686,449258786,453325943,89905716,271052672,785394913,382471423,510616456,438958157,173493988,103234191,107176446,266180664,1388144585,355867168],
   ![649845059,116215430,132759599,16082890,5938815,16082890,132759599,116215430,649845059,160506216,638962400,295326978,295326978,355867168,113772226,61579484,61579484,113772226,355867168,2572233787]]

def C : Matrix (Fin 20) (Fin 20) ℚ := fun i j => (CN i j : ℚ)/100000000

def diagLo : Fin 20 → ℤ :=
  ![6311804,8747054,14830986,7052727,6069388,7052727,14830986,8747054,
    6311804,4602496,15157569,2903005,2903005,12686842,3056711,988161,
    988161,3056711,12686842,5184665]
def diagHi : Fin 20 → ℤ :=
  ![6377012,8821188,14916061,7087691,6099354,7087691,14916061,8821188,
    6377012,4602540,15157612,2903041,2903041,12715311,3063125,990496,
    990496,3063125,12715311,5196584]

def offN (W : Fin 45 → ℤ) (i j : Fin 20) : ℤ :=
  if ((i.val < (11:Nat)) ∧ ((11:Nat) ≤ j.val)) ∨
      ((j.val < (11:Nat)) ∧ ((11:Nat) ≤ i.val)) then
    let f : Fin 9 := ⟨(max i.val j.val-11)%9,by omega⟩
    ∑ t : Fin 3,if (sourceFaces f t).val=min i.val j.val then
      W ⟨18+3*f.val+t.val,by omega⟩ else 0
  else 0
def AL (i j : Fin 20) : ℤ := if i=j then diagLo i else -offN hiN i j
def AH (i j : Fin 20) : ℤ := if i=j then diagHi i else -offN loN i j

def productZ (e : SourceEdge) (i j : Fin 20) : ℤ :=
  incidenceZ e (nodeEquiv.symm i)*incidenceZ e (nodeEquiv.symm j)
def lowerSum (i j : Fin 20) : ℤ :=
  ∑ e : SourceEdge,if 0≤productZ e i j then loN (srcFlat e)*productZ e i j
    else hiN (srcFlat e)*productZ e i j
def upperSum (i j : Fin 20) : ℤ :=
  ∑ e : SourceEdge,if 0≤productZ e i j then hiN (srcFlat e)*productZ e i j
    else loN (srcFlat e)*productZ e i j

def bindingRow (i : Fin 20) : Prop :=
  ∀ j : Fin 20,AL i j=lowerSum i j ∧ AH i j=upperSum i j

private theorem bind0 : bindingRow 0 := by intro j; fin_cases j <;> decide +kernel
private theorem bind1 : bindingRow 1 := by intro j; fin_cases j <;> decide +kernel
private theorem bind2 : bindingRow 2 := by intro j; fin_cases j <;> decide +kernel
private theorem bind3 : bindingRow 3 := by intro j; fin_cases j <;> decide +kernel
private theorem bind4 : bindingRow 4 := by intro j; fin_cases j <;> decide +kernel
private theorem bind5 : bindingRow 5 := by intro j; fin_cases j <;> decide +kernel
private theorem bind6 : bindingRow 6 := by intro j; fin_cases j <;> decide +kernel
private theorem bind7 : bindingRow 7 := by intro j; fin_cases j <;> decide +kernel
private theorem bind8 : bindingRow 8 := by intro j; fin_cases j <;> decide +kernel
private theorem bind9 : bindingRow 9 := by intro j; fin_cases j <;> decide +kernel
private theorem bind10 : bindingRow 10 := by intro j; fin_cases j <;> decide +kernel
private theorem bind11 : bindingRow 11 := by intro j; fin_cases j <;> decide +kernel
private theorem bind12 : bindingRow 12 := by intro j; fin_cases j <;> decide +kernel
private theorem bind13 : bindingRow 13 := by intro j; fin_cases j <;> decide +kernel
private theorem bind14 : bindingRow 14 := by intro j; fin_cases j <;> decide +kernel
private theorem bind15 : bindingRow 15 := by intro j; fin_cases j <;> decide +kernel
private theorem bind16 : bindingRow 16 := by intro j; fin_cases j <;> decide +kernel
private theorem bind17 : bindingRow 17 := by intro j; fin_cases j <;> decide +kernel
private theorem bind18 : bindingRow 18 := by intro j; fin_cases j <;> decide +kernel
private theorem bind19 : bindingRow 19 := by intro j; fin_cases j <;> decide +kernel

theorem table_binding (i j : Fin 20) : AL i j=lowerSum i j ∧ AH i j=upperSum i j := by
  fin_cases i
  · exact bind0 j
  · exact bind1 j
  · exact bind2 j
  · exact bind3 j
  · exact bind4 j
  · exact bind5 j
  · exact bind6 j
  · exact bind7 j
  · exact bind8 j
  · exact bind9 j
  · exact bind10 j
  · exact bind11 j
  · exact bind12 j
  · exact bind13 j
  · exact bind14 j
  · exact bind15 j
  · exact bind16 j
  · exact bind17 j
  · exact bind18 j
  · exact bind19 j

theorem CN_nonneg : ∀ i j : Fin 20,0≤CN i j := by decide +kernel

def RL (i j : Fin 20) : ℤ :=
  (if i=j then 10000000000000000 else 0)-∑ k : Fin 20,CN i k*AH k j
def RH (i j : Fin 20) : ℤ :=
  (if i=j then 10000000000000000 else 0)-∑ k : Fin 20,CN i k*AL k j
def rowCheck (i : Fin 20) : Prop :=
  50*(∑ j : Fin 20,max |RL i j| |RH i j|)≤10000000000000000

macro "row_eval" : tactic =>
  `(tactic| norm_num [rowCheck,RL,RH,CN,AL,AH,offN,lowerSum,upperSum,productZ,
    incidenceZ,SourceN2.spokeFlat,SourceN2.faceFlatEdge,ResumeLocalIncidence.sourceFaces,
    Fin.sum_univ_succ])
private theorem row0 : rowCheck 0 := by
  unfold rowCheck RL RH
  decide +kernel
private theorem row1 : rowCheck 1 := by
  unfold rowCheck RL RH
  decide +kernel
private theorem row2 : rowCheck 2 := by unfold rowCheck RL RH; decide +kernel
private theorem row3 : rowCheck 3 := by unfold rowCheck RL RH; decide +kernel
private theorem row4 : rowCheck 4 := by unfold rowCheck RL RH; decide +kernel
private theorem row5 : rowCheck 5 := by unfold rowCheck RL RH; decide +kernel
private theorem row6 : rowCheck 6 := by unfold rowCheck RL RH; decide +kernel
private theorem row7 : rowCheck 7 := by unfold rowCheck RL RH; decide +kernel
private theorem row8 : rowCheck 8 := by unfold rowCheck RL RH; decide +kernel
private theorem row9 : rowCheck 9 := by unfold rowCheck RL RH; decide +kernel
private theorem row10 : rowCheck 10 := by unfold rowCheck RL RH; decide +kernel
private theorem row11 : rowCheck 11 := by unfold rowCheck RL RH; decide +kernel
private theorem row12 : rowCheck 12 := by unfold rowCheck RL RH; decide +kernel
private theorem row13 : rowCheck 13 := by unfold rowCheck RL RH; decide +kernel
private theorem row14 : rowCheck 14 := by unfold rowCheck RL RH; decide +kernel
private theorem row15 : rowCheck 15 := by unfold rowCheck RL RH; decide +kernel
private theorem row16 : rowCheck 16 := by unfold rowCheck RL RH; decide +kernel
private theorem row17 : rowCheck 17 := by unfold rowCheck RL RH; decide +kernel
private theorem row18 : rowCheck 18 := by unfold rowCheck RL RH; decide +kernel
private theorem row19 : rowCheck 19 := by unfold rowCheck RL RH; decide +kernel

theorem all_rows (i : Fin 20) : rowCheck i := by
  fin_cases i
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7
  · exact row8
  · exact row9
  · exact row10
  · exact row11
  · exact row12
  · exact row13
  · exact row14
  · exact row15
  · exact row16
  · exact row17
  · exact row18
  · exact row19

end
end N11Formalization.SourceContractionProposal
#check @N11Formalization.SourceContractionProposal.table_binding
#check @N11Formalization.SourceContractionProposal.all_rows
#print axioms N11Formalization.SourceContractionProposal.table_binding
#print axioms N11Formalization.SourceContractionProposal.all_rows

