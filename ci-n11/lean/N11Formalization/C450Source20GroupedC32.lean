import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((2719999999:ℚ)/5000000000),((2997648049:ℚ)/5000000000),((3103999999:ℚ)/3560000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7730423359:ℚ)/10000000000),((-4715586575258205644375629223385620601648301517096521:ℚ)/35248450000000000000000000000000000000000000000000000),((-270789305688313341760598983:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((2957499999:ℚ)/5000000000),((6232957823:ℚ)/10000000000),((10024499997:ℚ)/11060000000),(1:ℚ),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3394296529:ℚ)/5000000000),((-10012499084012204963813929299878400334646465139791523:ℚ)/66059522265625000000000000000000000000000000000000000),((-266073373432297470835598983:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3076249999:ℚ)/5000000000),((3235304397:ℚ)/5000000000),((10380749997:ℚ)/11440000000),(1:ℚ),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((156857273:ℚ)/250000000),((-709090115797370421768464939885164169416453880760009667:ℚ)/4678731200000000000000000000000000000000000000000000000),((-260979194693259502433098983:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3194999999:ℚ)/5000000000),((411839411:ℚ)/625000000),((10736999997:ℚ)/11630000000),(1:ℚ),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5720564429:ℚ)/10000000000),((-785740144140734370006869898951426025908408190598614643:ℚ)/4915742959375000000000000000000000000000000000000000000),((-258663672590353273990598983:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3254374999:ℚ)/5000000000),((6708250049:ℚ)/10000000000),((3638374999:ℚ)/3940000000),(1:ℚ),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2712559939:ℚ)/5000000000),((-7630605742280187659896615364416871610572284653369001:ℚ)/47783581250000000000000000000000000000000000000000000),((-256131504503461478414348983:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3313749999:ℚ)/5000000000),((3413533661:ℚ)/5000000000),((11093249997:ℚ)/12010000000),(1:ℚ),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1278605897:ℚ)/2500000000),((-215943589499066499286580748537795691463116384872888387:ℚ)/1353377813281250000000000000000000000000000000000000000),((-253603610845879759588098983:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3373124999:ℚ)/5000000000),((1377295033:ℚ)/2000000000),((3757124999:ℚ)/4035000000),(1:ℚ),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((2392740191:ℚ)/5000000000),((-25174390395862502506794896476416853941193186854264443:ℚ)/153972053613281250000000000000000000000000000000000000),((-252460702177755624711848983:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3402812499:ℚ)/5000000000),((6945882497:ℚ)/10000000000),((11360437497:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((230647343:ℚ)/500000000),((-927250101298926604654921351855308605747236178428814247:ℚ)/5674525000000000000000000000000000000000000000000000000),((-251200481053287237334973983:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3432499999:ℚ)/5000000000),((7005289329:ℚ)/10000000000),((11449499997:ℚ)/12295000000),(1:ℚ),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((1108551099:ℚ)/2500000000),((-59285328357541240533640453704040116312727131237731723:ℚ)/363007533666992187500000000000000000000000000000000000),((-249941327374073537145598983:ℚ)/739328000000000000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3462187499:ℚ)/5000000000),((883086959:ℚ)/1250000000),((549455357:ℚ)/590000000),(1:ℚ),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((2124232987:ℚ)/5000000000),((-104764818234550204828736470322755396015187434492643:ℚ)/641809375000000000000000000000000000000000000000000),((-248683240884458501103723983:ℚ)/739328000000000000000000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3491874999:ℚ)/5000000000),((3591753469:ℚ)/5000000000),((683977941:ℚ)/740000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1013691691:ℚ)/2500000000),((-50421066675425350877010314025362786933779818012531:ℚ)/316581250000000000000000000000000000000000000000000),((-246045553277262793529348983:ℚ)/739328000000000000000000000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((1277:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3551249999:ℚ)/5000000000),((3651158189:ℚ)/5000000000),((11805749997:ℚ)/12770000000),(1:ℚ),((2337671911:ℚ)/2500000000),((9372267491:ℚ)/10000000000),((181171659:ℚ)/500000000),((3638335943:ℚ)/10000000000),((-64751962310805172862150439962022587018643467679637787:ℚ)/406726744726562500000000000000000000000000000000000000),((-243534734862432810823098983:ℚ)/739328000000000000000000000)⟩
theorem valid11 : Valid source20 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source20 nn0 nn1 Qcell ((629:ℚ)/800) ((1277:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1277:ℚ)/1600),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((3610624999:ℚ)/5000000000),((296844963:ℚ)/400000000),((3994624999:ℚ)/4320000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9350687649:ℚ)/10000000000),((735446993:ℚ)/2000000000),((3170332703:ℚ)/10000000000),((-13365796469545836935117475164949569363370242475502867:ℚ)/83980800000000000000000000000000000000000000000000000),((-241028180255567220386848983:ℚ)/739328000000000000000000000)⟩
theorem valid12 : Valid source20 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source20 nn0 nn1 Qcell ((1277:ℚ)/1600) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),((343:ℚ)/400),((15:ℚ)/16),(1:ℚ),((3669999999:ℚ)/5000000000),((7896338871:ℚ)/10000000000),((1737428571:ℚ)/1960000000),(1:ℚ),((57977633:ℚ)/62500000),((2332870371:ℚ)/2500000000),((1913736159:ℚ)/5000000000),((1311628491:ℚ)/5000000000),((-127836456825642553584929985535963227815710282781:ℚ)/919132812500000000000000000000000000000000000000),((-237129775830303464780598983:ℚ)/739328000000000000000000000)⟩
theorem valid13 : Valid source20 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((343:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((343:ℚ)/400),((181:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3907499999:ℚ)/5000000000),((4185765553:ℚ)/5000000000),((12874499997:ℚ)/14480000000),(1:ℚ),((9252071821:ℚ)/10000000000),((1855284257:ℚ)/2000000000),((1946075537:ℚ)/5000000000),(0:ℚ),((-1331076395405628245313679094732966248773914433449101427:ℚ)/9487585600000000000000000000000000000000000000000000000),((-329240233:ℚ)/1024000000)⟩
theorem valid14 : Valid source20 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source20 nn0 nn1 Qcell ((343:ℚ)/400) ((181:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((15:ℚ)/16),(1:ℚ),((4144999999:ℚ)/5000000000),((233046519:ℚ)/250000000),((13586999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-387059577038284095529830273690469225361496739976867547:ℚ)/3200000000000000000000000000000000000000000000000000000),((-329240233:ℚ)/1024000000)⟩
theorem valid15 : Valid source20 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source20 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4619999999:ℚ)/5000000000),((13122725359:ℚ)/10000000000),((5003999999:ℚ)/7360000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-2346243538689474696815564243985283:ℚ)/49836032000000000000000000000000000),((-329240233:ℚ)/1024000000)⟩
theorem valid16 : Valid source20 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((61:ℚ)/80) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source20 nn0 nn1 Qcell ((1239:ℚ)/1600) ((1277:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((1277:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source20 nn0 nn1 Qcell ((1277:ℚ)/1600) ((343:ℚ)/400) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source20 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source20 nn0 nn1 Qcell ((343:ℚ)/400) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source20 nn0 nn1 Qcell ((1277:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC32
#check @N11Formalization.C450Source20GroupedC32.bound
#print axioms N11Formalization.C450Source20GroupedC32.valid0
#print axioms N11Formalization.C450Source20GroupedC32.valid1
#print axioms N11Formalization.C450Source20GroupedC32.valid2
#print axioms N11Formalization.C450Source20GroupedC32.valid3
#print axioms N11Formalization.C450Source20GroupedC32.valid4
#print axioms N11Formalization.C450Source20GroupedC32.valid5
#print axioms N11Formalization.C450Source20GroupedC32.valid6
#print axioms N11Formalization.C450Source20GroupedC32.valid7
#print axioms N11Formalization.C450Source20GroupedC32.valid8
#print axioms N11Formalization.C450Source20GroupedC32.valid9
#print axioms N11Formalization.C450Source20GroupedC32.valid10
#print axioms N11Formalization.C450Source20GroupedC32.valid11
#print axioms N11Formalization.C450Source20GroupedC32.valid12
#print axioms N11Formalization.C450Source20GroupedC32.valid13
#print axioms N11Formalization.C450Source20GroupedC32.valid14
#print axioms N11Formalization.C450Source20GroupedC32.valid15
#print axioms N11Formalization.C450Source20GroupedC32.valid16
#print axioms N11Formalization.C450Source20GroupedC32.bound
#print axioms N11Formalization.C450Source20GroupedC32.endpoint_checks
