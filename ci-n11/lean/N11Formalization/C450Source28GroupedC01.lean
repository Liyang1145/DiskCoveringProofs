import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((2003:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((1432885697:ℚ)/2000000000),((3669687501:ℚ)/5000000000),(-1:ℚ),((-3607457091:ℚ)/4006000000),((398569427:ℚ)/400000000),(1:ℚ),((845998389:ℚ)/10000000000),((850499931:ℚ)/2500000000),((80673709719105957499415169877899:ℚ)/200600450000000000000000000000000),((4237870208833414410652289:ℚ)/3610000000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((2003:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((2003:ℚ)/3200),((1011:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((7223903933:ℚ)/10000000000),((7398750003:ℚ)/10000000000),(-1:ℚ),((-6071903933:ℚ)/6740000000),((9929701407:ℚ)/10000000000),((62276473:ℚ)/62500000),((18538009:ℚ)/156250000),((1579556067:ℚ)/5000000000),((5704602876967757181161685445938871:ℚ)/14196125000000000000000000000000000),((17021309772672122232745601:ℚ)/14440000000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((2003:ℚ)/3200) ((1011:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((455211093:ℚ)/625000000),((3729062501:ℚ)/5000000000),(-1:ℚ),((-1149633279:ℚ)/1275625000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((724166637:ℚ)/2500000000),((1933089279049757335985517186207:ℚ)/4814257812500000000000000000000),((4272832779106186229402289:ℚ)/3610000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((1835712301:ℚ)/2500000000),((3758750001:ℚ)/5000000000),(-1:ℚ),((-4643136903:ℚ)/5150000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((2608761393:ℚ)/10000000000),((9976685250410460635479493010623939:ℚ)/24864843750000000000000000000000000),((4290386217531146357527289:ℚ)/3610000000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((7402319131:ℚ)/10000000000),((3818125001:ℚ)/5000000000),(-1:ℚ),((-18750957393:ℚ)/20980000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2285790381:ℚ)/10000000000),((27852484056013870930024417593022631:ℚ)/68775062500000000000000000000000000),((1195251:ℚ)/1000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((940156727:ℚ)/1250000000),((3877500001:ℚ)/5000000000),(-1:ℚ),((-796156727:ℚ)/890000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((22512239:ℚ)/156250000),((6255309743819840477118267553181:ℚ)/15470703125000000000000000000000),((1195251:ℚ)/1000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((1528036383:ℚ)/2000000000),((8230000003:ℚ)/10000000000),(-1:ℚ),((-3892909149:ℚ)/4576000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((8331270554335131356774799768861311:ℚ)/19631040000000000000000000000000000),((1195251:ℚ)/1000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((8115835033:ℚ)/10000000000),((4590000001:ℚ)/5000000000),(-1:ℚ),((-6963835033:ℚ)/8640000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((3434876710406202379307589140410429:ℚ)/7776000000000000000000000000000000),((1195251:ℚ)/1000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((4533455541:ℚ)/5000000000),((11080000003:ℚ)/10000000000),(-1:ℚ),((-11872366623:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((111256854893397475075991365339158839:ℚ)/240000000000000000000000000000000000),((1195251:ℚ)/1000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((5484224551:ℚ)/5000000000),((14880000003:ℚ)/10000000000),(-1:ℚ),((-4908224551:ℚ)/7360000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((843401020637489056384977:ℚ)/1692800000000000000000000),((1195251:ℚ)/1000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
private theorem node0_2 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source28 nn0 nn1 Qcell ((2041:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source28 nn0 nn1 Qcell ((1011:ℚ)/1600) ((1049:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source28 nn0 nn1 Qcell ((1049:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source28 nn0 nn1 Qcell ((1049:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_10
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_10
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9]
theorem packet_count : packets.length = 10 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC01
#check @N11Formalization.C450Source28GroupedC01.bound
#print axioms N11Formalization.C450Source28GroupedC01.valid0
#print axioms N11Formalization.C450Source28GroupedC01.valid1
#print axioms N11Formalization.C450Source28GroupedC01.valid2
#print axioms N11Formalization.C450Source28GroupedC01.valid3
#print axioms N11Formalization.C450Source28GroupedC01.valid4
#print axioms N11Formalization.C450Source28GroupedC01.valid5
#print axioms N11Formalization.C450Source28GroupedC01.valid6
#print axioms N11Formalization.C450Source28GroupedC01.valid7
#print axioms N11Formalization.C450Source28GroupedC01.valid8
#print axioms N11Formalization.C450Source28GroupedC01.valid9
#print axioms N11Formalization.C450Source28GroupedC01.bound
#print axioms N11Formalization.C450Source28GroupedC01.endpoint_checks
