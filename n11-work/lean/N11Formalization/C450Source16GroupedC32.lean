import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((2799999999:ℚ)/5000000000),((6147154827:ℚ)/10000000000),((9295999997:ℚ)/10680000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7424089307:ℚ)/10000000000),((-2298148657445801690547542511830812296677031066482771:ℚ)/23792703750000000000000000000000000000000000000000000),((-11699670313303404000007359:ℚ)/38912000000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((6074999997:ℚ)/10000000000),((6384752621:ℚ)/10000000000),((20016999991:ℚ)/22120000000),(1:ℚ),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((805746001:ℚ)/1250000000),((-4302585217228671673132363063791430789656877412500819:ℚ)/39635713359375000000000000000000000000000000000000000),((-46120223300481369250066231:ℚ)/155648000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3156249999:ℚ)/5000000000),((1324468783:ℚ)/2000000000),((10364749997:ℚ)/11440000000),(1:ℚ),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((236250493:ℚ)/400000000),((-976877445274034322863159856623359488670093266449967:ℚ)/8997560000000000000000000000000000000000000000000000),((-11355656294665371812507359:ℚ)/38912000000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3274999999:ℚ)/5000000000),((6741137323:ℚ)/10000000000),((10720999997:ℚ)/11630000000),(1:ℚ),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5319057091:ℚ)/10000000000),((-14027129524421657666484371730096401223448448019293459:ℚ)/122893573984375000000000000000000000000000000000000000),((-11271372071722664150007359:ℚ)/38912000000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3334374999:ℚ)/5000000000),((1371985867:ℚ)/2000000000),((10899124997:ℚ)/11820000000),(1:ℚ),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2501203853:ℚ)/5000000000),((-1226215267308923805892759616286530940367718506718417:ℚ)/10751305781250000000000000000000000000000000000000000),((-11184356660945796043757359:ℚ)/38912000000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3393749999:ℚ)/5000000000),((6919324839:ℚ)/10000000000),((11077249997:ℚ)/11915000000),(1:ℚ),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1166560243:ℚ)/2500000000),((-46285671420022984485441024807463317871904162612448977:ℚ)/396454567001953125000000000000000000000000000000000000),((-11142345174397849087507359:ℚ)/38912000000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3423437499:ℚ)/5000000000),((6978720017:ℚ)/10000000000),((11166312497:ℚ)/12010000000),(1:ℚ),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((4489470389:ℚ)/10000000000),((-11843938213961909325287887921591282972090607511678293:ℚ)/101503335996093750000000000000000000000000000000000000),((-11098883496512229840632359:ℚ)/38912000000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3453124999:ℚ)/5000000000),((7038114879:ℚ)/10000000000),((11255374997:ℚ)/12105000000),(1:ℚ),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((4305960679:ℚ)/10000000000),((-12120962789451916171497793607410738581765336981823193:ℚ)/103931136188964843750000000000000000000000000000000000),((-11055435029454260081257359:ℚ)/38912000000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3482812499:ℚ)/5000000000),((887188679:ℚ)/1250000000),((11344437497:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2057403399:ℚ)/5000000000),((-49610147291938333058400466226826828835467788872085333:ℚ)/425589375000000000000000000000000000000000000000000000),((-579578935154013168914861:ℚ)/2048000000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((7024999997:ℚ)/10000000000),((3578451841:ℚ)/5000000000),((22866999991:ℚ)/24590000000),(1:ℚ),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((391488553:ℚ)/1000000000),((-8459137173537628128503070970215249468114857242690473:ℚ)/72601506733398437500000000000000000000000000000000000),((-43874310829445899750066231:ℚ)/155648000000000000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3542187499:ℚ)/5000000000),((7216297637:ℚ)/10000000000),((11522562497:ℚ)/12390000000),(1:ℚ),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((3704773979:ℚ)/10000000000),((-17306020368136445804153016868792056693731156465377799:ℚ)/148594915546875000000000000000000000000000000000000000),((-10925168841782977328132359:ℚ)/38912000000000000000000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3571874999:ℚ)/5000000000),((7335084687:ℚ)/10000000000),((11611624997:ℚ)/12580000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((3482624257:ℚ)/10000000000),((-780983929244076447843299313195340399513770063667801:ℚ)/6861898593750000000000000000000000000000000000000000),((-10836823493325819918757359:ℚ)/38912000000000000000000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((1277:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3631249999:ℚ)/5000000000),((1490774127:ℚ)/2000000000),((11789749997:ℚ)/12770000000),(1:ℚ),((2337671911:ℚ)/2500000000),((9372267491:ℚ)/10000000000),((181171659:ℚ)/500000000),((1495669091:ℚ)/5000000000),((-1156944842910359693118055874857648819272266771219131:ℚ)/10168168618164062500000000000000000000000000000000000),((-10750072105357864762507359:ℚ)/38912000000000000000000000)⟩
theorem valid12 : Valid source16 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source16 nn0 nn1 Qcell ((629:ℚ)/800) ((1277:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1277:ℚ)/1600),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((7381249997:ℚ)/10000000000),((7572655527:ℚ)/10000000000),((23935749991:ℚ)/25920000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9350687649:ℚ)/10000000000),((735446993:ℚ)/2000000000),((481015931:ℚ)/2000000000),((-51588442573733100977884270239584094721885105369028659:ℚ)/453496320000000000000000000000000000000000000000000000),((-42653493613025143387566231:ℚ)/155648000000000000000000000)⟩
theorem valid13 : Valid source16 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source16 nn0 nn1 Qcell ((1277:ℚ)/1600) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3749999999:ℚ)/5000000000),((8522901693:ℚ)/10000000000),((12145999997:ℚ)/14480000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((81199913:ℚ)/500000000),((-3784635620619460378314343759327070666964007955516153:ℚ)/44473057500000000000000000000000000000000000000000000),((-560312098286568815789861:ℚ)/2048000000000000000000000)⟩
theorem valid14 : Valid source16 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((15:ℚ)/16),(1:ℚ),((4224999999:ℚ)/5000000000),((592068817:ℚ)/625000000),((13570999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-7047264891569400882933831175450137215238538776998011:ℚ)/80000000000000000000000000000000000000000000000000000),((-56045831:ℚ)/204800000)⟩
theorem valid15 : Valid source16 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source16 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4699999999:ℚ)/5000000000),((3318406007:ℚ)/2500000000),((14995999997:ℚ)/22080000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1278964258050100722694716699994033:ℚ)/33639321600000000000000000000000000),((-56045831:ℚ)/204800000)⟩
theorem valid16 : Valid source16 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((2383:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source16 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((2421:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source16 nn0 nn1 Qcell ((2421:ℚ)/3200) ((2459:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source16 nn0 nn1 Qcell ((2459:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source16 nn0 nn1 Qcell ((2421:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source16 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source16 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source16 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source16 nn0 nn1 Qcell ((2421:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC32
#check @N11Formalization.C450Source16GroupedC32.bound
#print axioms N11Formalization.C450Source16GroupedC32.valid0
#print axioms N11Formalization.C450Source16GroupedC32.valid1
#print axioms N11Formalization.C450Source16GroupedC32.valid2
#print axioms N11Formalization.C450Source16GroupedC32.valid3
#print axioms N11Formalization.C450Source16GroupedC32.valid4
#print axioms N11Formalization.C450Source16GroupedC32.valid5
#print axioms N11Formalization.C450Source16GroupedC32.valid6
#print axioms N11Formalization.C450Source16GroupedC32.valid7
#print axioms N11Formalization.C450Source16GroupedC32.valid8
#print axioms N11Formalization.C450Source16GroupedC32.valid9
#print axioms N11Formalization.C450Source16GroupedC32.valid10
#print axioms N11Formalization.C450Source16GroupedC32.valid11
#print axioms N11Formalization.C450Source16GroupedC32.valid12
#print axioms N11Formalization.C450Source16GroupedC32.valid13
#print axioms N11Formalization.C450Source16GroupedC32.valid14
#print axioms N11Formalization.C450Source16GroupedC32.valid15
#print axioms N11Formalization.C450Source16GroupedC32.valid16
#print axioms N11Formalization.C450Source16GroupedC32.bound
#print axioms N11Formalization.C450Source16GroupedC32.endpoint_checks
