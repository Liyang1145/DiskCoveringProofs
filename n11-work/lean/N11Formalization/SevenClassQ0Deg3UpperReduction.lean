import N11Formalization.SevenClassQ0Deg3UpperTables

/-! Lane A: finite-bin reduction of the q0 degree-three upper tables.

The generated tables currently expose 30 all-grid obligations.  This module
replaces each 2049-point family by eight right-endpoint checks together with
an explicit monotonicity premise on each bin.  The premises are kept visible;
they are the analytic derivative-sign obligations, not hidden finite scans. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3UpperReduction

open MetricAreaRationalCertificate
open SevenClassQ0Deg3Bins
open SevenClassQ0Deg3UpperTables

def EdgeBinMono : Prop :=
  ∀ (i : Fin 21) (k : Fin 2049),
    edgeUpper (∑ j ∈ tableEdges i, mu j) (nodeQ RatInterval.piHi 2048 k) ≤
      edgeUpper (∑ j ∈ tableEdges i, mu j)
        (nodeQ RatInterval.piHi 2048 (binHi (binIndex k)))

def SectorBinMono : Prop :=
  ∀ (i : Fin 9) (k : Fin 2049),
    sectorUpper (mu (nextSite i)) lam (nodeQ RatInterval.piHi 2048 k) (nodeBin k) ≤
      sectorUpper (mu (nextSite i)) lam
        (nodeQ RatInterval.piHi 2048 (binHi (binIndex k)))
        (nodeBin (binHi (binIndex k)))

def EdgeEndpointValid : Prop :=
  ∀ (i : Fin 21) (j : Fin 8), EdgeCheck i (binHi j)

def SectorEndpointValid : Prop :=
  ∀ (i : Fin 9) (j : Fin 8), SectorCheck i (binHi j)

theorem edgeValid_of_binMono (hm : EdgeBinMono) (he : EdgeEndpointValid) :
    EdgeValid := by
  intro i k
  exact (hm i k).trans (he i (binIndex k))

theorem sectorValid_of_binMono (hm : SectorBinMono) (he : SectorEndpointValid) :
    SectorValid := by
  intro i k
  exact (hm i k).trans (he i (binIndex k))

end N11Formalization.SevenClassQ0Deg3UpperReduction
#check @N11Formalization.SevenClassQ0Deg3UpperReduction.edgeValid_of_binMono
#check @N11Formalization.SevenClassQ0Deg3UpperReduction.sectorValid_of_binMono
