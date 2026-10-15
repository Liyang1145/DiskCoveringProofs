import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((2779999999:ℚ)/5000000000),((3054616877:ℚ)/5000000000),((3099999999:ℚ)/3560000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7501612473:ℚ)/10000000000),((-3729815369229329922458587284746290004227350882887327:ℚ)/35248450000000000000000000000000000000000000000000000),((-234073394050896530040219351:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((6034999997:ℚ)/10000000000),((1586711507:ℚ)/2500000000),((20024999991:ℚ)/22120000000),(1:ℚ),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6533056029:ℚ)/10000000000),((-63033063630537808489203993123570895316294037702277527:ℚ)/528476178125000000000000000000000000000000000000000000),((-921881077252789305091974159:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3136249999:ℚ)/5000000000),((3292225419:ℚ)/5000000000),((10368749997:ℚ)/11440000000),(1:ℚ),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((600011809:ℚ)/1000000000),((-558106215129461246830974729912429530619578128383071029:ℚ)/4678731200000000000000000000000000000000000000000000000),((-226725533941573033552719351:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3254999999:ℚ)/5000000000),((6703250673:ℚ)/10000000000),((10724999997:ℚ)/11630000000),(1:ℚ),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1084386669:ℚ)/2000000000),((-617184350001153854413997007870848586911357415151143941:ℚ)/4915742959375000000000000000000000000000000000000000000),((-224939541105412484190219351:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3314374999:ℚ)/5000000000),((1364409781:ℚ)/2000000000),((3634374999:ℚ)/3940000000),(1:ℚ),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1022212421:ℚ)/2000000000),((-5994431448646521880024227038183126276852216229793087:ℚ)/47783581250000000000000000000000000000000000000000000),((-223072655088110423433969351:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3373749999:ℚ)/5000000000),((1720361861:ℚ)/2500000000),((11081249997:ℚ)/11915000000),(1:ℚ),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((4781907447:ℚ)/10000000000),((-679175148620342522069396842833813444059040006071607741:ℚ)/5286060893359375000000000000000000000000000000000000000),((-222183547815430664227719351:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3403437499:ℚ)/5000000000),((694084561:ℚ)/1000000000),((11170312497:ℚ)/12010000000),(1:ℚ),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((4609250343:ℚ)/10000000000),((-173787590968861397192295493456669428191970574813757169:ℚ)/1353377813281250000000000000000000000000000000000000000),((-221251473691428976505844351:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3433124999:ℚ)/5000000000),((7000243413:ℚ)/10000000000),((3753124999:ℚ)/4035000000),(1:ℚ),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((886073849:ℚ)/2000000000),((-19760829308596013257198473940855268236583832554676541:ℚ)/153972053613281250000000000000000000000000000000000000),((-220319792182300745771469351:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3462812499:ℚ)/5000000000),((352982043:ℚ)/500000000),((11348437497:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2122236943:ℚ)/5000000000),((-727896293670454129268110812918520276814457164809269489:ℚ)/5674525000000000000000000000000000000000000000000000000),((-219388503173001184824594351:ℚ)/739328000000000000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((6984999997:ℚ)/10000000000),((177975949:ℚ)/250000000),((22874999991:ℚ)/24590000000),(1:ℚ),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((810119023:ℚ)/2000000000),((-372336181637931446142719057411362265179442135914807327:ℚ)/2904060269335937500000000000000000000000000000000000000),((-873830426059397935591974159:ℚ)/2957312000000000000000000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3522187499:ℚ)/5000000000),((7178434721:ℚ)/10000000000),((3842187499:ℚ)/4130000000),(1:ℚ),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((3847522553:ℚ)/10000000000),((-28211880055459114142019028125333194515280476537769763:ℚ)/220140615625000000000000000000000000000000000000000000),((-217527102078664136293344351:ℚ)/739328000000000000000000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3551874999:ℚ)/5000000000),((912153407:ℚ)/1250000000),((11615624997:ℚ)/12580000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((3633711263:ℚ)/10000000000),((-194680389610520429722090750383061431572932065756207861:ℚ)/1555363681250000000000000000000000000000000000000000000),((-215620816550633727108969351:ℚ)/739328000000000000000000000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((1277:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3611249999:ℚ)/5000000000),((296640741:ℚ)/400000000),((11793749997:ℚ)/12770000000),(1:ℚ),((2337671911:ℚ)/2500000000),((9372267491:ℚ)/10000000000),((181171659:ℚ)/500000000),((1582526309:ℚ)/5000000000),((-50892216723223479231298712163714150044707994913517469:ℚ)/406726744726562500000000000000000000000000000000000000),((-213761777949614834902719351:ℚ)/739328000000000000000000000)⟩
theorem valid12 : Valid source17 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source17 nn0 nn1 Qcell ((629:ℚ)/800) ((1277:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1277:ℚ)/1600),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((7341249997:ℚ)/10000000000),((7534808583:ℚ)/10000000000),((7981249997:ℚ)/8640000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9350687649:ℚ)/10000000000),((735446993:ℚ)/2000000000),((65422679:ℚ)/250000000),((-84045631840897752781686582047115658113391827286819583:ℚ)/671846400000000000000000000000000000000000000000000000),((-847617223385827767129474159:ℚ)/2957312000000000000000000000)⟩
theorem valid13 : Valid source17 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source17 nn0 nn1 Qcell ((1277:ℚ)/1600) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3729999999:ℚ)/5000000000),((8485091187:ℚ)/10000000000),((12149999997:ℚ)/14480000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((1922388529:ℚ)/10000000000),((-55074433813852968135813864882507840479493186971876549:ℚ)/592974100000000000000000000000000000000000000000000000),((-210929272376263641540219351:ℚ)/739328000000000000000000000)⟩
theorem valid14 : Valid source17 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((15:ℚ)/16),(1:ℚ),((4204999999:ℚ)/5000000000),((9435320077:ℚ)/10000000000),((13574999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-307926083769459386777680656312982694252195387066906589:ℚ)/3200000000000000000000000000000000000000000000000000000),((-58461189:ℚ)/204800000)⟩
theorem valid15 : Valid source17 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source17 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4679999999:ℚ)/5000000000),((3308980107:ℚ)/2500000000),((4999999999:ℚ)/7360000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1996948874253993944256642119989621:ℚ)/49836032000000000000000000000000000),((-58461189:ℚ)/204800000)⟩
theorem valid16 : Valid source17 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((2383:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source17 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((2421:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source17 nn0 nn1 Qcell ((2421:ℚ)/3200) ((2459:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source17 nn0 nn1 Qcell ((2459:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source17 nn0 nn1 Qcell ((2421:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source17 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source17 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source17 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source17 nn0 nn1 Qcell ((2421:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC32
#check @N11Formalization.C450Source17GroupedC32.bound
#print axioms N11Formalization.C450Source17GroupedC32.valid0
#print axioms N11Formalization.C450Source17GroupedC32.valid1
#print axioms N11Formalization.C450Source17GroupedC32.valid2
#print axioms N11Formalization.C450Source17GroupedC32.valid3
#print axioms N11Formalization.C450Source17GroupedC32.valid4
#print axioms N11Formalization.C450Source17GroupedC32.valid5
#print axioms N11Formalization.C450Source17GroupedC32.valid6
#print axioms N11Formalization.C450Source17GroupedC32.valid7
#print axioms N11Formalization.C450Source17GroupedC32.valid8
#print axioms N11Formalization.C450Source17GroupedC32.valid9
#print axioms N11Formalization.C450Source17GroupedC32.valid10
#print axioms N11Formalization.C450Source17GroupedC32.valid11
#print axioms N11Formalization.C450Source17GroupedC32.valid12
#print axioms N11Formalization.C450Source17GroupedC32.valid13
#print axioms N11Formalization.C450Source17GroupedC32.valid14
#print axioms N11Formalization.C450Source17GroupedC32.valid15
#print axioms N11Formalization.C450Source17GroupedC32.valid16
#print axioms N11Formalization.C450Source17GroupedC32.bound
#print axioms N11Formalization.C450Source17GroupedC32.endpoint_checks
