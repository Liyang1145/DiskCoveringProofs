import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((6063345899:ℚ)/10000000000),((3287946333:ℚ)/5000000000),((7503345899:ℚ)/26700000000),((3927946333:ℚ)/9920000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1617861207:ℚ)/2500000000),((289680314571926902927398484651695743761:ℚ)/17397928747008000000000000000000000000000),((-13436794740584831080346917:ℚ)/115520000000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((817397077:ℚ)/1250000000),((3406852991:ℚ)/5000000000),((997397077:ℚ)/3456250000),((1348950997:ℚ)/3560000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2673535001:ℚ)/5000000000),((3835214642475394257329053693524241657328336215283773963121:ℚ)/258703037905200000000000000000000000000000000000000000000000),((-216471656534841679921793:ℚ)/1805000000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((6777049059:ℚ)/10000000000),((433287793:ℚ)/625000000),((913005451:ℚ)/3125000000),((513287793:ℚ)/1382500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((939343141:ℚ)/2000000000),((33142980301586864900630144730678289241201413490569:ℚ)/2359268652343750000000000000000000000000000000000000),((-42190662823951080888072031:ℚ)/346560000000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((1:ℚ)/4),((5:ℚ)/16),((430998489:ℚ)/625000000),((6992052169:ℚ)/10000000000),((520998489:ℚ)/1772656250),((2757350723:ℚ)/7500000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((135569817:ℚ)/312500000),((185828355330522359495828105266957732490005608967127911208813:ℚ)/13574779980468750000000000000000000000000000000000000000000000),((-459933591746744526961:ℚ)/3750000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((3477718491:ℚ)/5000000000),((1410299689:ℚ)/2000000000),((4197718491:ℚ)/14300000000),((1666299689:ℚ)/4538000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((4148195121:ℚ)/10000000000),((6509863191916276698560923297085776427591799102606767239:ℚ)/477755349095882000000000000000000000000000000000000000000),((-10665657514229436791433631:ℚ)/86640000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/4),((5:ℚ)/16),((1402979341:ℚ)/2000000000),((888867943:ℚ)/1250000000),((1690979341:ℚ)/5767500000),((1048867943:ℚ)/2860000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((15428047:ℚ)/39062500),((879704297993856136361931409664793839531840972397375448771:ℚ)/64847324089762500000000000000000000000000000000000000000000),((-570934963311338057840277:ℚ)/4620800000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((707435503:ℚ)/1000000000),((896298437:ℚ)/1250000000),((851435503:ℚ)/2907500000),((352099479:ℚ)/961250000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((233813701:ℚ)/625000000),((4057151685081959677294532831010869999602110049347579161:ℚ)/300336763612559082031250000000000000000000000000000000000),((-143258998269416661458653:ℚ)/1155200000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/4),((5:ℚ)/16),((7133811991:ℚ)/10000000000),((7229830329:ℚ)/10000000000),((8573811991:ℚ)/29312500000),((8509830329:ℚ)/23260000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1760370733:ℚ)/5000000000),((174576268708468696957773808092513302060943806300753715407173:ℚ)/12975260845045012500000000000000000000000000000000000000000000),((-39829512316034535358357:ℚ)/320000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((7193267621:ℚ)/10000000000),((728927207:ℚ)/1000000000),((8633267621:ℚ)/29550000000),((856927207:ℚ)/2345000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1643193577:ℚ)/5000000000),((94326951660800002694352242331240158133245756353665353657:ℚ)/7037582984615039062500000000000000000000000000000000000000),((-14431036467381487778331397:ℚ)/115520000000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/4),((5:ℚ)/16),((7252721953:ℚ)/10000000000),((1469742549:ℚ)/2000000000),((8692721953:ℚ)/29787500000),((1725742549:ℚ)/4728000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1517346059:ℚ)/5000000000),((150287387840555157644440250422057532132718895999383794408873:ℚ)/11253348288114422400000000000000000000000000000000000000000000),((-14483647418044073908319053:ℚ)/115520000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((7312175017:ℚ)/10000000000),((7408152379:ℚ)/10000000000),((8752175017:ℚ)/30025000000),((8688152379:ℚ)/23830000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((690228193:ℚ)/2500000000),((101477872715062722779047586955908743933509119463852883315389:ℚ)/7624619518642455859375000000000000000000000000000000000000000),((-14536286822708352359192413:ℚ)/115520000000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((7371626843:ℚ)/10000000000),((7527028623:ℚ)/10000000000),((8811626843:ℚ)/30500000000),((8807028623:ℚ)/24020000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((614418513:ℚ)/2500000000),((4340183512272212426604199704029434507375928546544216995577:ℚ)/322298805966050000000000000000000000000000000000000000000000),((-14588954706066186472030533:ℚ)/115520000000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((74905269:ℚ)/100000000),((1941192413:ℚ)/2500000000),((89305269:ℚ)/314500000),((2261192413:ℚ)/6100000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1699356917:ℚ)/10000000000),((1931648960912860374535826000393114521593774450537620037787:ℚ)/140317171595312500000000000000000000000000000000000000000000),((-4408312802112451217911:ℚ)/34656000000000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((7728313391:ℚ)/10000000000),((8002496527:ℚ)/10000000000),((9168313391:ℚ)/32400000000),((9282496527:ℚ)/25160000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((8893968712731438550812961919240916623160999647443893470177:ℚ)/653103431211600000000000000000000000000000000000000000000000),((-8194761:ℚ)/64000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((1991520763:ℚ)/2500000000),((2475980789:ℚ)/2500000000),((2351520763:ℚ)/10000000000),((2795980789:ℚ)/6480000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((5563714867794279313203509930782954643625404547741833:ℚ)/318864600000000000000000000000000000000000000000000000),((-8194761:ℚ)/64000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((123347233:ℚ)/125000000),((6852798563:ℚ)/5000000000),((141347233:ℚ)/690000000),((7492798563:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((110915751369847212530548132200048422159:ℚ)/4875264000000000000000000000000000000000),((-8194761:ℚ)/64000000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC21
#check @N11Formalization.C450Source11GroupedC21.bound
#print axioms N11Formalization.C450Source11GroupedC21.valid0
#print axioms N11Formalization.C450Source11GroupedC21.valid1
#print axioms N11Formalization.C450Source11GroupedC21.valid2
#print axioms N11Formalization.C450Source11GroupedC21.valid3
#print axioms N11Formalization.C450Source11GroupedC21.valid4
#print axioms N11Formalization.C450Source11GroupedC21.valid5
#print axioms N11Formalization.C450Source11GroupedC21.valid6
#print axioms N11Formalization.C450Source11GroupedC21.valid7
#print axioms N11Formalization.C450Source11GroupedC21.valid8
#print axioms N11Formalization.C450Source11GroupedC21.valid9
#print axioms N11Formalization.C450Source11GroupedC21.valid10
#print axioms N11Formalization.C450Source11GroupedC21.valid11
#print axioms N11Formalization.C450Source11GroupedC21.valid12
#print axioms N11Formalization.C450Source11GroupedC21.valid13
#print axioms N11Formalization.C450Source11GroupedC21.valid14
#print axioms N11Formalization.C450Source11GroupedC21.valid15
#print axioms N11Formalization.C450Source11GroupedC21.bound
#print axioms N11Formalization.C450Source11GroupedC21.endpoint_checks
