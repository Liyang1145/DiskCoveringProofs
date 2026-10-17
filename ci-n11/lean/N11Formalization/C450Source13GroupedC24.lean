import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((5946048817:ℚ)/10000000000),((6470763561:ℚ)/10000000000),((16220780573:ℚ)/35600000000),((7430763561:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1680816161:ℚ)/2500000000),((31774974900367902460071:ℚ)/7120000000000000000000000),((-707248685229113057253198543:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((6422043603:ℚ)/10000000000),((1677166869:ℚ)/2500000000),((51994305221:ℚ)/110600000000),((639055623:ℚ)/1112500000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2821102157:ℚ)/5000000000),((243044953157507277770148616116654851:ℚ)/183485400000000000000000000000000000000),((-718889226476911167970262983:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/16),((1:ℚ)/2),((6659989581:ℚ)/10000000000),((853451147:ℚ)/1250000000),((53659927067:ℚ)/112500000000),((973451147:ℚ)/1728125000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2513193807:ℚ)/5000000000),((-3605680882598902628171177786854109:ℚ)/63281250000000000000000000000000000000),((-724723034018899338218140807:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((6778951241:ℚ)/10000000000),((3473272247:ℚ)/5000000000),((54492658687:ℚ)/114400000000),((3953272247:ℚ)/7031250000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((146599457:ℚ)/312500000),((-13025528417850735421480584795700829:ℚ)/65436800000000000000000000000000000000),((-727643357600862369110334047:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((6897905853:ℚ)/10000000000),((7065473743:ℚ)/10000000000),((55325340971:ℚ)/116300000000),((8025473743:ℚ)/14300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4332188677:ℚ)/10000000000),((-33109404227585654470289768841993371:ℚ)/101442675000000000000000000000000000000),((-730565972835294439506194983:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((7:ℚ)/16),((1:ℚ)/2),((3508426881:ℚ)/5000000000),((890617023:ℚ)/1250000000),((28078988167:ℚ)/58625000000),((1010617023:ℚ)/1817187500),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((492860267:ℚ)/1250000000),((-23897092410687326264621332804323467:ℚ)/25776679687500000000000000000000000000),((-183372721942799995104777007:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((3538162653:ℚ)/5000000000),((224512413:ℚ)/312500000),((28287138571:ℚ)/59100000000),((509024826:ℚ)/916015625),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3733918629:ℚ)/10000000000),((-8504261961461979357144993937693741:ℚ)/8732025000000000000000000000000000000),((-508971059581012071383503:ℚ)/2560000000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((7:ℚ)/16),((1:ℚ)/2),((3567897647:ℚ)/5000000000),((3621928437:ℚ)/5000000000),((28495283529:ℚ)/59575000000),((1367309479:ℚ)/2462500000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3513166181:ℚ)/10000000000),((-54176546199871120467255916646695609:ℚ)/53237709375000000000000000000000000000),((-184104527504599972012867983:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((7195263763:ℚ)/10000000000),((7303315189:ℚ)/10000000000),((57406846341:ℚ)/120100000000),((8263315189:ℚ)/14893750000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3278239657:ℚ)/10000000000),((-19081464439767124916956752583870603:ℚ)/18030012500000000000000000000000000000),((-737882588584462248514757703:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/16),((1:ℚ)/2),((7254730751:ℚ)/10000000000),((3681386097:ℚ)/5000000000),((57823115257:ℚ)/121050000000),((4161386097:ℚ)/7506250000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((94557333:ℚ)/312500000),((-80301849396740805450107646221876147:ℚ)/73265512500000000000000000000000000000),((-739347646622351270425175087:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((7314196291:ℚ)/10000000000),((92777849:ℚ)/125000000),((58239374037:ℚ)/122000000000),((104777849:ℚ)/189140625),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((550227899:ℚ)/2000000000),((-84159717925343288224946333898431907:ℚ)/74420000000000000000000000000000000000),((-740813284899565087230878247:ℚ)/3696640000000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((3686830209:ℚ)/5000000000),((7541135649:ℚ)/10000000000),((29327811463:ℚ)/61950000000),((8501135649:ℚ)/15250000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1223326051:ℚ)/5000000000),((-6746085781495646404422580403519623:ℚ)/9594506250000000000000000000000000000),((-185569876058573721943827247:ℚ)/924160000000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((7492584563:ℚ)/10000000000),((1532007721:ℚ)/2000000000),((59488091941:ℚ)/125800000000),((1724007721:ℚ)/3097500000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1683272371:ℚ)/10000000000),((-1897642230715822566241273911076471:ℚ)/2472756250000000000000000000000000000),((-745213689109491388997687303:ℚ)/3696640000000000000000000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((1902875859:ℚ)/2500000000),((7897831037:ℚ)/10000000000),((15080131013:ℚ)/32400000000),((8857831037:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((216576467114550693717453638421469:ℚ)/5248800000000000000000000000000000000),((-51791277:ℚ)/256000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((3924663149:ℚ)/5000000000),((9799669749:ℚ)/10000000000),((30992642043:ℚ)/80000000000),((132835429:ℚ)/200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((218188333107005995215969356629392407:ℚ)/24000000000000000000000000000000000000),((-51791277:ℚ)/256000000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((4875678131:ℚ)/5000000000),((13601826961:ℚ)/10000000000),((12549915639:ℚ)/36800000000),((14561826961:ℚ)/20000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((12228029801567043198501831:ℚ)/677120000000000000000000000),((-51791277:ℚ)/256000000)⟩
theorem valid15 : Valid source13 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((2383:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((2383:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source13 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source13 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source13 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source13 nn0 nn1 Qcell ((2383:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC24
#check @N11Formalization.C450Source13GroupedC24.bound
#print axioms N11Formalization.C450Source13GroupedC24.valid0
#print axioms N11Formalization.C450Source13GroupedC24.valid1
#print axioms N11Formalization.C450Source13GroupedC24.valid2
#print axioms N11Formalization.C450Source13GroupedC24.valid3
#print axioms N11Formalization.C450Source13GroupedC24.valid4
#print axioms N11Formalization.C450Source13GroupedC24.valid5
#print axioms N11Formalization.C450Source13GroupedC24.valid6
#print axioms N11Formalization.C450Source13GroupedC24.valid7
#print axioms N11Formalization.C450Source13GroupedC24.valid8
#print axioms N11Formalization.C450Source13GroupedC24.valid9
#print axioms N11Formalization.C450Source13GroupedC24.valid10
#print axioms N11Formalization.C450Source13GroupedC24.valid11
#print axioms N11Formalization.C450Source13GroupedC24.valid12
#print axioms N11Formalization.C450Source13GroupedC24.valid13
#print axioms N11Formalization.C450Source13GroupedC24.valid14
#print axioms N11Formalization.C450Source13GroupedC24.valid15
#print axioms N11Formalization.C450Source13GroupedC24.bound
#print axioms N11Formalization.C450Source13GroupedC24.endpoint_checks
