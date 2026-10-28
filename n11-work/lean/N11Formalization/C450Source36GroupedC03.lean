import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((290163981:ℚ)/400000000),((1876823673:ℚ)/2500000000),((-10417765711:ℚ)/12400000000),((-2876131753:ℚ)/4044000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((378577581:ℚ)/1250000000),((4120306632298116174689177276078085859:ℚ)/7944504976728000000000000000000000000),((26258537032687208807411707:ℚ)/28880000000000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((3686906903:ℚ)/5000000000),((7626720963:ℚ)/10000000000),((-42507046741:ℚ)/50550000000),((-36729789739:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((2445818767:ℚ)/10000000000),((14089964947022444921765863003811821322797324795102186198649659:ℚ)/27268047215991210937500000000000000000000000000000000000000000),((1822709:ℚ)/2000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((7493492093:ℚ)/10000000000),((7865500737:ℚ)/10000000000),((-44178505159:ℚ)/51500000000),((-25005132403:ℚ)/35600000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1676129719:ℚ)/10000000000),((3099600688020059235103287820908267173897818408235590719227:ℚ)/5842981344531250000000000000000000000000000000000000000000),((1822709:ℚ)/2000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((1933187121:ℚ)/2500000000),((4171401693:ℚ)/5000000000),((-23759811851:ℚ)/26700000000),((-19531432573:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((965065201988508887848848262226121576360025029717490227132031:ℚ)/1737198273525000000000000000000000000000000000000000000000000),((1822709:ℚ)/2000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((8210907751:ℚ)/10000000000),((9296593711:ℚ)/10000000000),((-54196155977:ℚ)/57200000000),((-84341800763:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((62420679782601549128913568325940981219885755613610236138972409:ℚ)/104327395286400000000000000000000000000000000000000000000000000),((1822709:ℚ)/2000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((9166105691:ℚ)/10000000000),((5601002407:ℚ)/5000000000),(-1:ℚ),((-96759373983:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((508934344463670852297873460058380327859892607472381956183:ℚ)/800000000000000000000000000000000000000000000000000000000),((1822709:ℚ)/2000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((11073521703:ℚ)/10000000000),((3752086483:ℚ)/2500000000),(-1:ℚ),((-121555782139:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((895585659879833608199445010497507995593:ℚ)/1345572864000000000000000000000000000000),((1822709:ℚ)/2000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
private theorem node1_3 :
    CellBound source36 nn0 nn1 Qcell ((1011:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((81:ℚ)/100) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_3 node3_7
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_7
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6]
theorem packet_count : packets.length = 7 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC03
#check @N11Formalization.C450Source36GroupedC03.bound
#print axioms N11Formalization.C450Source36GroupedC03.valid0
#print axioms N11Formalization.C450Source36GroupedC03.valid1
#print axioms N11Formalization.C450Source36GroupedC03.valid2
#print axioms N11Formalization.C450Source36GroupedC03.valid3
#print axioms N11Formalization.C450Source36GroupedC03.valid4
#print axioms N11Formalization.C450Source36GroupedC03.valid5
#print axioms N11Formalization.C450Source36GroupedC03.valid6
#print axioms N11Formalization.C450Source36GroupedC03.bound
#print axioms N11Formalization.C450Source36GroupedC03.endpoint_checks
