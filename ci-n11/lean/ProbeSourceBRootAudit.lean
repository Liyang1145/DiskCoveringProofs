import N11Formalization
set_option autoImplicit false
open N11Formalization
open SourceBMatrixIntervals SourceBPointPacket

#check @SourceBMatrixIntervals.auxBox_mem
#check @SourceBMatrixIntervals.nodeBox_mem
#check @SourceBMatrixIntervals.BBox_mem
#check @SourceBMatrixIntervals.actual_mass_row
#check @SourceBPointPacket.pointI_contains
#check @SourceBPointPacket.pointI_mem

#print SourceBMatrixIntervals.BBox
#print SourceBPointPacket.pointI
#print axioms SourceBMatrixIntervals.BBox_mem
#print axioms SourceBPointPacket.pointI_mem

-- Correct source graph: all41 rows/all45 edges, including the two real hubs.
example (i : Fin 41) (e : Fin 45) :
    (BBox i e).Mem (SourceN2.srcB2 SourceExactRoot.sourceRoot i e) :=
  BBox_mem i e

example (i : Fin 29) (q : Fin 2) :
    (pointI i q).Mem
      ((SourceN2.srcX2 SourceExactRoot.sourceRoot i).ofLp q) :=
  pointI_mem i q

example (e : Fin 45) :
    SourceN2.srcB2 SourceExactRoot.sourceRoot 40 e = 1 :=
  actual_mass_row e

example : SourceN2.srcB2 SourceExactRoot.sourceRoot 18 19 =
    SourceN2.srcB2 SourceExactRoot.sourceRoot 18 19 := rfl

#check @SourceExactRoot.source_attainment
#check @SourceExactRoot.main_of_lower_bound
#print axioms SourceExactRoot.source_attainment
