import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((6388227899:ℚ)/10000000000),((834668867:ℚ)/1250000000),((-4722682069:ℚ)/12400000000),((-14364683697:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((715608763:ℚ)/1250000000),((19877839051943475856806790883924804743237534704441115721:ℚ)/330806025390625000000000000000000000000000000000000000000),((597463346285866746542837:ℚ)/5120000000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((828316727:ℚ)/1250000000),((106195509:ℚ)/156250000),((-603368563:ℚ)/1609375000),((-1884950181:ℚ)/6556250000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5117020453:ℚ)/10000000000),((33155476101218386635198118182197007951472329470786149:ℚ)/566935667262077331542968750000000000000000000000000000),((172602357589830961475287:ℚ)/1520000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((6745664773:ℚ)/10000000000),((864457437:ℚ)/1250000000),((-4931202059:ℚ)/13112500000),((-5145664773:ℚ)/17800000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4787152313:ℚ)/10000000000),((6746496057166940966726731377918488424934863813627586691:ℚ)/115548825156250000000000000000000000000000000000000000000),((10893582387355498248122287:ℚ)/97280000000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((6864782113:ℚ)/10000000000),((7034792473:ℚ)/10000000000),((-40283547311:ℚ)/106800000000),((-15794346339:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4434872577:ℚ)/10000000000),((65076851622838866131755484412979431645489146130370989757:ℚ)/1116294236005859375000000000000000000000000000000000000000),((10740384557145933114744007:ℚ)/97280000000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((6983886553:ℚ)/10000000000),((7094353961:ℚ)/10000000000),((-40700477727:ℚ)/108700000000),((-316699209:ℚ)/1075000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4054311233:ℚ)/10000000000),((1518963423066913983154119462499873256155982944416201:ℚ)/26374544982910156250000000000000000000000000000000000),((10586956555392749292927127:ℚ)/97280000000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((3521717073:ℚ)/5000000000),((7153912231:ℚ)/10000000000),((-41117385617:ℚ)/109650000000),((-8165151219:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((962704887:ℚ)/2500000000),((1085765290428812968629043027964986592830342422362660127:ℚ)/18863090146942138671875000000000000000000000000000000000),((138291526232161171015773:ℚ)/1280000000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((3551489381:ℚ)/5000000000),((1803366841:ℚ)/2500000000),((-1483366841:ℚ)/3950000000),((-8254468143:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1818282651:ℚ)/5000000000),((481302026606447322789340680884029027251456417768098879:ℚ)/8366154660120010375976562500000000000000000000000000000),((2608324399599840677788783:ℚ)/24320000000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((7162520477:ℚ)/10000000000),((3636509721:ℚ)/5000000000),((-20975568047:ℚ)/55775000000),((-5562520477:ℚ)/18750000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((340951563:ℚ)/1000000000),((774181588011084336086733742321346525897971204526697503:ℚ)/13464018702507019042968750000000000000000000000000000000),((10356381280691520357420287:ℚ)/97280000000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((1805514841:ℚ)/2500000000),((7332568541:ℚ)/10000000000),((-14122659929:ℚ)/37500000000),((-4216544523:ℚ)/14181250000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((3166914857:ℚ)/10000000000),((32012929921496565166459479790980132746060151839781:ℚ)/557023578119277954101562500000000000000000000000000),((642462934694933667821143:ℚ)/6080000000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((910199437:ℚ)/1250000000),((462007171:ℚ)/625000000),((-2674050197:ℚ)/7090625000),((-2130598311:ℚ)/7150000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2904864159:ℚ)/10000000000),((286313607258524333068702862944099181418311926258661281:ℚ)/4984244052734375000000000000000000000000000000000000000),((159412102124640765220607:ℚ)/1520000000000000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((367056447:ℚ)/500000000),((75111987:ℚ)/100000000),((-436183909:ℚ)/1144000000),((-861169341:ℚ)/2907500000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2617522771:ℚ)/10000000000),((15924137842775537854080439672584343929682695352069149:ℚ)/274590329371337890625000000000000000000000000000000000),((25313209862577282653127:ℚ)/243200000000000000000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((3730094017:ℚ)/5000000000),((1907567971:ℚ)/2500000000),((-11112975797:ℚ)/29075000000),((-2930094017:ℚ)/9850000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((960546557:ℚ)/5000000000),((1257486057732745750198025293851621472648528374863818053:ℚ)/21707931638183593750000000000000000000000000000000000000),((2492731982700614719874567:ℚ)/24320000000000000000000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/16),((-3:ℚ)/8),((7579237153:ℚ)/10000000000),((245887123:ℚ)/312500000),((-480403287:ℚ)/1231250000),((-17937711459:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((739350851:ℚ)/10000000000),((205907293313071222245464878446680559611638700149179155241:ℚ)/3493379453125000000000000000000000000000000000000000000000),((9816338318672658501577927:ℚ)/97280000000000000000000000)⟩
theorem valid12 : Valid source16 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((390865367:ℚ)/500000000),((4172255639:ℚ)/5000000000),((-24725789473:ℚ)/61000000000),((-103621789:ℚ)/360000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((4503796189930393097044950243047285883338009794261:ℚ)/74115000000000000000000000000000000000000000000000),((6440363:ℚ)/64000000)⟩
theorem valid13 : Valid source16 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((8293347077:ℚ)/10000000000),((2561983677:ℚ)/2500000000),((-15693885739:ℚ)/32400000000),((-20080041231:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((75701739019052945321624349787012956978235844727269293379:ℚ)/1080000000000000000000000000000000000000000000000000000000),((6440363:ℚ)/64000000)⟩
theorem valid14 : Valid source16 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((5098257953:ℚ)/5000000000),((7025974547:ℚ)/5000000000),((-44701821829:ℚ)/80000000000),((-4298257953:ℚ)/18400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((9782103562733681465177609488492967279738835490447039:ℚ)/121670000000000000000000000000000000000000000000000000),((6440363:ℚ)/64000000)⟩
theorem valid15 : Valid source16 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source16 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source16 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source16 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC10
#check @N11Formalization.C450Source16GroupedC10.bound
#print axioms N11Formalization.C450Source16GroupedC10.valid0
#print axioms N11Formalization.C450Source16GroupedC10.valid1
#print axioms N11Formalization.C450Source16GroupedC10.valid2
#print axioms N11Formalization.C450Source16GroupedC10.valid3
#print axioms N11Formalization.C450Source16GroupedC10.valid4
#print axioms N11Formalization.C450Source16GroupedC10.valid5
#print axioms N11Formalization.C450Source16GroupedC10.valid6
#print axioms N11Formalization.C450Source16GroupedC10.valid7
#print axioms N11Formalization.C450Source16GroupedC10.valid8
#print axioms N11Formalization.C450Source16GroupedC10.valid9
#print axioms N11Formalization.C450Source16GroupedC10.valid10
#print axioms N11Formalization.C450Source16GroupedC10.valid11
#print axioms N11Formalization.C450Source16GroupedC10.valid12
#print axioms N11Formalization.C450Source16GroupedC10.valid13
#print axioms N11Formalization.C450Source16GroupedC10.valid14
#print axioms N11Formalization.C450Source16GroupedC10.valid15
#print axioms N11Formalization.C450Source16GroupedC10.bound
#print axioms N11Formalization.C450Source16GroupedC10.endpoint_checks
