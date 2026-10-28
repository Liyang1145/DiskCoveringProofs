import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((5:ℚ)/8),((11:ℚ)/16),((5217951511:ℚ)/10000000000),((1111896321:ℚ)/2000000000),((7265951511:ℚ)/10300000000),((16454859531:ℚ)/19840000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((8140319221:ℚ)/10000000000),((-1771927825982443005872538795566702737313239420482467212941:ℚ)/5027386163200000000000000000000000000000000000000000000000),((-1127391577668073992771121:ℚ)/2334720000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((5458233459:ℚ)/10000000000),((1449947443:ℚ)/2500000000),((7506233459:ℚ)/10680000000),((21229421873:ℚ)/25750000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1924001629:ℚ)/2500000000),((-2516111670039948064175726979088880227831984931475508055203:ℚ)/7123000708007812500000000000000000000000000000000000000000),((-10999391199389901468433337:ℚ)/23104000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((2849157099:ℚ)/5000000000),((5919868979:ℚ)/10000000000),((3873157099:ℚ)/5435000000),((86238558769:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7230695387:ℚ)/10000000000),((-1009634796860461040778370078103310413556056114205682133716597:ℚ)/2758684690800000000000000000000000000000000000000000000000000),((-174791743117061327493786633:ℚ)/369664000000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((727285731:ℚ)/1250000000),((3019950887:ℚ)/5000000000),((983285731:ℚ)/1382500000),((43779459757:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3494394591:ℚ)/5000000000),((-1359549235362855251686290960706883101428842132117565479033:ℚ)/3715754690075683593750000000000000000000000000000000000000),((-43366147599850734751142097:ℚ)/92416000000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/8),((11:ℚ)/16),((2969107449:ℚ)/5000000000),((6159890559:ℚ)/10000000000),((3993107449:ℚ)/5625000000),((88878796149:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3369898997:ℚ)/5000000000),((-108735391795151681081100768549200835096201444072809596717:ℚ)/297267850195312500000000000000000000000000000000000000000),((-516327858717996422125399459:ℚ)/1108992000000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((6058103547:ℚ)/10000000000),((6219869153:ℚ)/10000000000),((8106103547:ℚ)/11345000000),((89538560683:ℚ)/112500000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6482877067:ℚ)/10000000000),((-18742559293769199500057315251491834346001934748831954957279:ℚ)/50479156494140625000000000000000000000000000000000000000000),((-171471241233926183548096417:ℚ)/369664000000000000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((764754171:ℚ)/1250000000),((6279837571:ℚ)/10000000000),((1020754171:ℚ)/1430000000),((90198213281:ℚ)/113450000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((6351134583:ℚ)/10000000000),((-484386321607634072585894133931168543467254207063323259139351:ℚ)/1305057225458593750000000000000000000000000000000000000000000),((-170775990187092635149235433:ℚ)/369664000000000000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((6177953847:ℚ)/10000000000),((633979607:ℚ)/1000000000),((8225953847:ℚ)/11535000000),((825979607:ℚ)/1040000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((6217014721:ℚ)/10000000000),((-235070010880112049830195395948879107074429341286453:ℚ)/633559875000000000000000000000000000000000000000000),((-1700737040983428046533937:ℚ)/3696640000000000000000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((3118932609:ℚ)/5000000000),((3199872449:ℚ)/5000000000),((4142932609:ℚ)/5815000000),((45758596939:ℚ)/57675000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1216071331:ℚ)/2000000000),((-172409056328899272544634001589549725975929196106533611504867:ℚ)/464837639297167968750000000000000000000000000000000000000000),((-42341095888851167723327713:ℚ)/92416000000000000000000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((5:ℚ)/8),((11:ℚ)/16),((629776771:ℚ)/1000000000),((3229842147:ℚ)/5000000000),((119225253:ℚ)/167500000),((46088263617:ℚ)/58150000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1188196339:ℚ)/2000000000),((-30529113221219968479295905898698497274980307695345194350843:ℚ)/82338694569531250000000000000000000000000000000000000000000),((-126486021853953610200685051:ℚ)/277248000000000000000000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((3178830771:ℚ)/5000000000),((651961449:ℚ)/1000000000),((4202830771:ℚ)/5910000000),((9283575939:ℚ)/11725000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((724836297:ℚ)/1250000000),((-551709043000382945964837781986243032034594053213680897973:ℚ)/1488490478979492187500000000000000000000000000000000000000),((-5037739241884853138541139:ℚ)/11089920000000000000000000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((3208773463:ℚ)/5000000000),((1659862043:ℚ)/2500000000),((4232773463:ℚ)/6005000000),((23538482473:ℚ)/29550000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((5653258897:ℚ)/10000000000),((-269385422581597897760665222411093025301499596107430414151:ℚ)/737378579882812500000000000000000000000000000000000000000),((-10400416124332915434666137:ℚ)/23104000000000000000000000)⟩
theorem valid11 : Valid source34 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((1307458633:ℚ)/2000000000),((135184953:ℚ)/200000000),((1717058633:ℚ)/2440000000),((1909434483:ℚ)/2402000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((668991399:ℚ)/1250000000),((-1929658933746030482632558826975148183820998841137285599:ℚ)/5283586983050000000000000000000000000000000000000000000),((-197892805010704117326451:ℚ)/443596800000000000000000)⟩
theorem valid12 : Valid source34 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source34 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source34 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((1331401599:ℚ)/2000000000),((6998750303:ℚ)/10000000000),((1741001599:ℚ)/2516000000),((98106253333:ℚ)/122000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1006905057:ℚ)/2000000000),((-1901993036344324616571399374791927195507845813362753573076067:ℚ)/5353914337500000000000000000000000000000000000000000000000000),((-161734166356879044505763617:ℚ)/369664000000000000000000000)⟩
theorem valid13 : Valid source34 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((862043651:ℚ)/1250000000),((3619067057:ℚ)/5000000000),((372681217:ℚ)/540000000),((50369737627:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2168532601:ℚ)/5000000000),((-403488253011705923597202247186649969343023275123274370941:ℚ)/1134995118750000000000000000000000000000000000000000000000),((-39636350705778729041622337:ℚ)/92416000000000000000000000)⟩
theorem valid14 : Valid source34 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source34 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((7135581263:ℚ)/10000000000),((1143744347:ℚ)/1250000000),((9183581263:ℚ)/16000000000),((15221187817:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((219624027:ℚ)/625000000),((-1126847118318122033435816288812711223049243917092901843:ℚ)/4982259375000000000000000000000000000000000000000000000),((-403700412191548897:ℚ)/972800000000000000)⟩
theorem valid15 : Valid source34 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((2261612947:ℚ)/2500000000),((12963778553:ℚ)/10000000000),((924537649:ℚ)/1840000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-243639101647743:ℚ)/1840000000000000),((-26626527:ℚ)/64000000)⟩
theorem valid16 : Valid source34 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source34 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((2307:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source34 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source34 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source34 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source34 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source34 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source34 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source34 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC27
#check @N11Formalization.C450Source34GroupedC27.bound
#print axioms N11Formalization.C450Source34GroupedC27.valid0
#print axioms N11Formalization.C450Source34GroupedC27.valid1
#print axioms N11Formalization.C450Source34GroupedC27.valid2
#print axioms N11Formalization.C450Source34GroupedC27.valid3
#print axioms N11Formalization.C450Source34GroupedC27.valid4
#print axioms N11Formalization.C450Source34GroupedC27.valid5
#print axioms N11Formalization.C450Source34GroupedC27.valid6
#print axioms N11Formalization.C450Source34GroupedC27.valid7
#print axioms N11Formalization.C450Source34GroupedC27.valid8
#print axioms N11Formalization.C450Source34GroupedC27.valid9
#print axioms N11Formalization.C450Source34GroupedC27.valid10
#print axioms N11Formalization.C450Source34GroupedC27.valid11
#print axioms N11Formalization.C450Source34GroupedC27.valid12
#print axioms N11Formalization.C450Source34GroupedC27.valid13
#print axioms N11Formalization.C450Source34GroupedC27.valid14
#print axioms N11Formalization.C450Source34GroupedC27.valid15
#print axioms N11Formalization.C450Source34GroupedC27.valid16
#print axioms N11Formalization.C450Source34GroupedC27.bound
#print axioms N11Formalization.C450Source34GroupedC27.endpoint_checks
