import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((2868199637:ℚ)/5000000000),((6276132689:ℚ)/10000000000),((9644598911:ℚ)/13350000000),((90549724957:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((894329191:ℚ)/1250000000),((-1777027473428317278266289526422249499:ℚ)/39654506250000000000000000000000000000),((-64054624826516196988758893:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((776501509:ℚ)/1250000000),((3256968869:ℚ)/5000000000),((2589504527:ℚ)/3456250000),((15606865099:ℚ)/17800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6139652639:ℚ)/10000000000),((-13437590054583697705170210842923690380348167050614073:ℚ)/258045008850097656250000000000000000000000000000000000),((-15933961189058458780631413:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((6449786833:ℚ)/10000000000),((1687930621:ℚ)/2500000000),((21429360499:ℚ)/28600000000),((24183098073:ℚ)/27650000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((2786784179:ℚ)/5000000000),((-7642092093222045760372924591537351363214677698720768261:ℚ)/146210350000000000000000000000000000000000000000000000000),((-3963519707940102552408253:ℚ)/14440000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((417971457:ℚ)/625000000),((6870607867:ℚ)/10000000000),((1383914371:ℚ)/1817187500),((98277902271:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4950606251:ℚ)/10000000000),((-520549391462860334385880379276700986897725806528481:ℚ)/9376035612821578979492187500000000000000000000000000),((-63256268824966412354205637:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((850801907:ℚ)/1250000000),((6989488891:ℚ)/10000000000),((2812405721:ℚ)/3693750000),((99823355583:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2305305109:ℚ)/5000000000),((-1457511691531761129163857296541170996454154366370213:ℚ)/26248305130004882812500000000000000000000000000000000),((-63096034089055956418847173:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((277011331:ℚ)/400000000),((7048927833:ℚ)/10000000000),((914233993:ℚ)/1191500000),((100596061829:ℚ)/118200000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((4245565587:ℚ)/10000000000),((-603421848298865978879511791248540984761607510893527:ℚ)/10572121786718750000000000000000000000000000000000000),((-63015846052873894277370237:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((698471587:ℚ)/1000000000),((3554182881:ℚ)/5000000000),((2303414761:ℚ)/3002500000),((50684377453:ℚ)/59575000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((810308739:ℚ)/2000000000),((-603339478763028524684604973735700705199404956518311:ℚ)/10573264166259765625000000000000000000000000000000000),((-15733902715624502365324413:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((7044147553:ℚ)/10000000000),((3583901351:ℚ)/5000000000),((23212442659:ℚ)/30262500000),((51070717563:ℚ)/60050000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((3848319827:ℚ)/10000000000),((-365994893999830897449679219519528420902008421360747007:ℚ)/6415502233886718750000000000000000000000000000000000000),((-15713832121995535267494733:ℚ)/57760000000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((1420715669:ℚ)/2000000000),((289089547:ℚ)/400000000),((4678147007:ℚ)/6100000000),((1372188037:ℚ)/1614000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((908586667:ℚ)/2500000000),((-80910250240581325563273060213237738015999836738052913:ℚ)/1418631250000000000000000000000000000000000000000000000),((-100439998243208961509797:ℚ)/369664000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((7163008267:ℚ)/10000000000),((7346107813:ℚ)/10000000000),((3367003543:ℚ)/4425000000),((104459401569:ℚ)/122000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1703797837:ℚ)/5000000000),((-2506247059256396929243775026541035953982632887010059:ℚ)/45127221679687500000000000000000000000000000000000000),((-62614197979260530274231877:ℚ)/231040000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((7281865581:ℚ)/10000000000),((7464973347:ℚ)/10000000000),((23925596743:ℚ)/31450000000),((106004653511:ℚ)/123900000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1451811573:ℚ)/5000000000),((-10544174803438753607165868011047738394877346937242433:ℚ)/189863730621337890625000000000000000000000000000000000),((-62453207881011420171497397:ℚ)/231040000000000000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((7400719649:ℚ)/10000000000),((7702694239:ℚ)/10000000000),((24282158947:ℚ)/32400000000),((109095025107:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2295059823:ℚ)/10000000000),((-138525249722324844103100094859957356731027260308695717:ℚ)/2624400000000000000000000000000000000000000000000000000),((-34498667:ℚ)/128000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((381920931:ℚ)/500000000),((2401020813:ℚ)/2500000000),((1249762793:ℚ)/2000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-79978235982610471740630587708066527038951879579223:ℚ)/3125000000000000000000000000000000000000000000000000),((-34498667:ℚ)/128000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((9539669827:ℚ)/10000000000),((2681142621:ℚ)/2000000000),((30699009481:ℚ)/55200000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-129368929184990530478868767742704639:ℚ)/14016384000000000000000000000000000000),((-34498667:ℚ)/128000000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source15 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC29
#check @N11Formalization.C450Source15GroupedC29.bound
#print axioms N11Formalization.C450Source15GroupedC29.valid0
#print axioms N11Formalization.C450Source15GroupedC29.valid1
#print axioms N11Formalization.C450Source15GroupedC29.valid2
#print axioms N11Formalization.C450Source15GroupedC29.valid3
#print axioms N11Formalization.C450Source15GroupedC29.valid4
#print axioms N11Formalization.C450Source15GroupedC29.valid5
#print axioms N11Formalization.C450Source15GroupedC29.valid6
#print axioms N11Formalization.C450Source15GroupedC29.valid7
#print axioms N11Formalization.C450Source15GroupedC29.valid8
#print axioms N11Formalization.C450Source15GroupedC29.valid9
#print axioms N11Formalization.C450Source15GroupedC29.valid10
#print axioms N11Formalization.C450Source15GroupedC29.valid11
#print axioms N11Formalization.C450Source15GroupedC29.valid12
#print axioms N11Formalization.C450Source15GroupedC29.valid13
#print axioms N11Formalization.C450Source15GroupedC29.bound
#print axioms N11Formalization.C450Source15GroupedC29.endpoint_checks
