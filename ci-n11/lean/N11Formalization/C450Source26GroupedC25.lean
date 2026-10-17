import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((1395531043:ℚ)/2500000000),((6143022349:ℚ)/10000000000),((1875531043:ℚ)/3337500000),((71287201141:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1864703611:ℚ)/2500000000),((-803982289200331829494939597917289:ℚ)/9294024902343750000000000000000000),((-118749783815963019316877:ℚ)/288800000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6061096547:ℚ)/10000000000),((3191160747:ℚ)/5000000000),((7981096547:ℚ)/13825000000),((36720446723:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((647635221:ℚ)/1000000000),((-5165759856530495518148249707959792446743081253869150969:ℚ)/49544641699218750000000000000000000000000000000000000000),((-90207002869463261521229:ℚ)/216600000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/2),((9:ℚ)/16),((630037567:ℚ)/1000000000),((50796289:ℚ)/78125000),((822037567:ℚ)/1406250000),((582166601:ℚ)/864062500),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((92732009:ℚ)/156250000),((-650113552903432657075950658282218299207776936398949:ℚ)/5793571472167968750000000000000000000000000000000000),((-7563840447199436643233:ℚ)/18050000000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((1604992419:ℚ)/2500000000),((1655374961:ℚ)/2500000000),((2084992419:ℚ)/3575000000),((18898374649:ℚ)/28125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5647305231:ℚ)/10000000000),((-2911146459605315288449130746266011362401540847902481:ℚ)/25960644531250000000000000000000000000000000000000000),((-7567667105402382688567:ℚ)/18050000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((6539535357:ℚ)/10000000000),((421315467:ℚ)/625000000),((8459535357:ℚ)/14537500000),((4791839203:ℚ)/7150000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5346143639:ℚ)/10000000000),((-537774021196444276615861546517543230798596300304749213:ℚ)/4800530233764648437500000000000000000000000000000000000),((-45424777835077274749813:ℚ)/108300000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((166476853:ℚ)/250000000),((6860569207:ℚ)/10000000000),((214476853:ℚ)/369375000),((77745122863:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5028887471:ℚ)/10000000000),((-26428866842598495200339958576210413195968087412399:ℚ)/236234746170043945312500000000000000000000000000000),((-121171657183477263085173:ℚ)/288800000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((6778587281:ℚ)/10000000000),((6980066293:ℚ)/10000000000),((8698587281:ℚ)/15012500000),((78820596637:ℚ)/118200000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((234612089:ℚ)/500000000),((-7085764875174083268040228843697724805569121594730577763:ℚ)/63439584997558593750000000000000000000000000000000000000),((-121199430427092459841173:ℚ)/288800000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((6898076069:ℚ)/10000000000),((887442487:ℚ)/1250000000),((8818076069:ℚ)/15250000000),((9986982383:ℚ)/15012500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4331655127:ℚ)/10000000000),((-2471041018790940228918501983755382115283929593706195549:ℚ)/22166113281250000000000000000000000000000000000000000000),((-15152008496568990835879:ℚ)/36100000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((7017541637:ℚ)/10000000000),((7338420959:ℚ)/10000000000),((8937541637:ℚ)/15725000000),((82045788631:ℚ)/122000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((492565671:ℚ)/1250000000),((-635561420608272970011036782029620462318620844261605093:ℚ)/6075639379882812500000000000000000000000000000000000000),((-120544106325007105292637:ℚ)/288800000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((725640737:ℚ)/1000000000),((7577220367:ℚ)/10000000000),((917640737:ℚ)/1620000000),((84194983303:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((603684519:ℚ)/2000000000),((-102639301615313177911846926293890002961166860711331:ℚ)/984150000000000000000000000000000000000000000000000),((-120499768299661223892853:ℚ)/288800000000000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((7495192363:ℚ)/10000000000),((2371345019:ℚ)/2500000000),((9415192363:ℚ)/20000000000),((25342105171:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((332533209:ℚ)/2000000000),((-59123812326140384640759085964603873:ℚ)/1500000000000000000000000000000000000),((-51245553203104851:ℚ)/121600000000000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((9403261697:ℚ)/10000000000),((13294933759:ℚ)/10000000000),((11323261697:ℚ)/27600000000),((135654403831:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((6526601347224539615421119:ℚ)/380880000000000000000000000),((-6775497:ℚ)/16000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source26 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source26 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC25
#check @N11Formalization.C450Source26GroupedC25.bound
#print axioms N11Formalization.C450Source26GroupedC25.valid0
#print axioms N11Formalization.C450Source26GroupedC25.valid1
#print axioms N11Formalization.C450Source26GroupedC25.valid2
#print axioms N11Formalization.C450Source26GroupedC25.valid3
#print axioms N11Formalization.C450Source26GroupedC25.valid4
#print axioms N11Formalization.C450Source26GroupedC25.valid5
#print axioms N11Formalization.C450Source26GroupedC25.valid6
#print axioms N11Formalization.C450Source26GroupedC25.valid7
#print axioms N11Formalization.C450Source26GroupedC25.valid8
#print axioms N11Formalization.C450Source26GroupedC25.valid9
#print axioms N11Formalization.C450Source26GroupedC25.valid10
#print axioms N11Formalization.C450Source26GroupedC25.valid11
#print axioms N11Formalization.C450Source26GroupedC25.bound
#print axioms N11Formalization.C450Source26GroupedC25.endpoint_checks
