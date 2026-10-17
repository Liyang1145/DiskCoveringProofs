import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((451535071:ℚ)/625000000),((7474353713:ℚ)/10000000000),((-41760475991:ℚ)/49600000000),((-1503318641:ℚ)/2106250000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((3156327591:ℚ)/10000000000),((2315619619679000957698411089792580146001:ℚ)/4597514454125000000000000000000000000000),((104260303471414492527853663:ℚ)/115520000000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((3672109443:ℚ)/5000000000),((1518748317:ℚ)/2000000000),((-2839746073:ℚ)/3370000000),((-36857422759:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((2601764929:ℚ)/10000000000),((3042590328230563611965054041307796664671312946805060301421631:ℚ)/6059566047998046875000000000000000000000000000000000000000000),((4183814056437377581014903:ℚ)/4620800000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((298553711:ℚ)/400000000),((7832448723:ℚ)/10000000000),((-44267141061:ℚ)/51500000000),((-3010798243:ℚ)/4272000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1895741289:ℚ)/10000000000),((1153895905120221126834394478094857776295262146783292043:ℚ)/2243704836300000000000000000000000000000000000000000000),((28978651:ℚ)/32000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((3851498151:ℚ)/5000000000),((8309620779:ℚ)/10000000000),((-15869115151:ℚ)/17800000000),((-3562679633:ℚ)/5200000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((3733968712611495616774532291524500107563620079556373153577:ℚ)/6960974800000000000000000000000000000000000000000000000000),((28978651:ℚ)/32000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((8180970737:ℚ)/10000000000),((2315799099:ℚ)/2500000000),((-13570593693:ℚ)/14300000000),((-84592619581:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((13311004307802885325906421964348118872462292273525138044031423:ℚ)/23183865619200000000000000000000000000000000000000000000000000),((28978651:ℚ)/32000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((9135865067:ℚ)/10000000000),((11168301461:ℚ)/10000000000),(-1:ℚ),((-97006245871:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((970823125658361679623618179823342339614245945494711282559:ℚ)/1600000000000000000000000000000000000000000000000000000000),((28978651:ℚ)/32000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((220856977:ℚ)/200000000),((3743571133:ℚ)/2500000000),(-1:ℚ),((-2435940701:ℚ)/4416000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1508397033408575330959600329345103:ℚ)/2392129536000000000000000000000000),((28978651:ℚ)/32000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
private theorem node1_3 :
    CellBound source35 nn0 nn1 Qcell ((1011:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((81:ℚ)/100) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_3 node3_7
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_7
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6]
theorem packet_count : packets.length = 7 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC03
#check @N11Formalization.C450Source35GroupedC03.bound
#print axioms N11Formalization.C450Source35GroupedC03.valid0
#print axioms N11Formalization.C450Source35GroupedC03.valid1
#print axioms N11Formalization.C450Source35GroupedC03.valid2
#print axioms N11Formalization.C450Source35GroupedC03.valid3
#print axioms N11Formalization.C450Source35GroupedC03.valid4
#print axioms N11Formalization.C450Source35GroupedC03.valid5
#print axioms N11Formalization.C450Source35GroupedC03.valid6
#print axioms N11Formalization.C450Source35GroupedC03.bound
#print axioms N11Formalization.C450Source35GroupedC03.endpoint_checks
