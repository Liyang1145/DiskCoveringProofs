import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((6072899157:ℚ)/10000000000),((329109937:ℚ)/500000000),((6968899157:ℚ)/21360000000),((35978381:ℚ)/80000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1612641747:ℚ)/2500000000),((94403850993253129310372781671161:ℚ)/9124992000000000000000000000000000),((-880200632523067689581542967:ℚ)/8871936000000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((6548404979:ℚ)/10000000000),((3409940509:ℚ)/5000000000),((7444404979:ℚ)/22120000000),((11509821527:ℚ)/26700000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5323193661:ℚ)/10000000000),((976315946356777468887704747355697847297424146990238216008987:ℚ)/109140344116256250000000000000000000000000000000000000000000000),((-300296280659044808010059501:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/16),((3:ℚ)/8),((848266473:ℚ)/1250000000),((1387743507:ℚ)/2000000000),((960266473:ℚ)/2812500000),((4675230521:ℚ)/11060000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4670241131:ℚ)/10000000000),((816075244025233110129463780007082928038024469605917129:ℚ)/97843589550000000000000000000000000000000000000000000000),((-14239522990736264134288607:ℚ)/138624000000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((5:ℚ)/16),((3:ℚ)/8),((6904989433:ℚ)/10000000000),((1399626941:ℚ)/2000000000),((7800989433:ℚ)/22690000000),((4710880823:ℚ)/11250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((4309932581:ℚ)/10000000000),((369226323757623923473893410435173182756273873796997935871641:ℚ)/45814882434082031250000000000000000000000000000000000000000000),((-305524648400961530169806229:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((6964416903:ℚ)/10000000000),((3528775587:ℚ)/5000000000),((7860416903:ℚ)/22880000000),((11866326761:ℚ)/28362500000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1029694829:ℚ)/2500000000),((71862853246767944989755596469491961063153973331864939729:ℚ)/8972268425027832031250000000000000000000000000000000000000),((-919202224894036529505690047:ℚ)/8871936000000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((5:ℚ)/16),((3:ℚ)/8),((7023843501:ℚ)/10000000000),((88962087:ℚ)/125000000),((7919843501:ℚ)/23070000000),((298886261:ℚ)/715000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3918871671:ℚ)/10000000000),((8067519789064175520133071231721793651983992201946919401:ℚ)/1013239438902539062500000000000000000000000000000000000000),((-921834534240972790133646983:ℚ)/8871936000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((55338041:ℚ)/78125000),((3588191039:ℚ)/5000000000),((62338041:ℚ)/181718750),((12044573117:ℚ)/28837500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3708790387:ℚ)/10000000000),((21399959424313805932664616869220585156558286990180815377153:ℚ)/2703030872513031738281250000000000000000000000000000000000000),((-18808408080992900435141:ℚ)/180500000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((5:ℚ)/16),((3:ℚ)/8),((1785673541:ℚ)/2500000000),((3617898273:ℚ)/5000000000),((2009673541:ℚ)/5862500000),((12133694819:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((27893543:ℚ)/80000000),((199548697413514425718234610093951657629960732560413493713591:ℚ)/25342306337978540039062500000000000000000000000000000000000000),((-19314817601595074217706141:ℚ)/184832000000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((7202118271:ℚ)/10000000000),((7295210379:ℚ)/10000000000),((2699372757:ℚ)/7880000000),((24445631137:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((325011229:ℚ)/1000000000),((95708395236831668107540974461686335483603829205490099716831:ℚ)/12218026014956665039062500000000000000000000000000000000000000),((-309918549229626319177838501:ℚ)/2957312000000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((5:ℚ)/16),((3:ℚ)/8),((1815385397:ℚ)/2500000000),((919327949:ℚ)/1250000000),((2039385397:ℚ)/5957500000),((3077983847:ℚ)/7387500000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((748903619:ℚ)/2500000000),((334611640089296332034678973113705549937123060971120080690547:ℚ)/42928116943795861816406250000000000000000000000000000000000000),((-19425085064900637042791549:ℚ)/184832000000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((7320964133:ℚ)/10000000000),((7414036199:ℚ)/10000000000),((8216964133:ℚ)/24020000000),((24802108597:ℚ)/59575000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((271816629:ℚ)/1000000000),((924251548778612622542671379187118693533493528791737193287611:ℚ)/119134679978788372802734375000000000000000000000000000000000000),((-311685517265824267927118429:ℚ)/2957312000000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((295215437:ℚ)/400000000),((941607457:ℚ)/1250000000),((331055437:ℚ)/976000000),((3144822371:ℚ)/7506250000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1204924067:ℚ)/5000000000),((38761520986414971687466703307487473820834130943972156631:ℚ)/4917889495331573486328125000000000000000000000000000000000),((-500113629027803091142509:ℚ)/4731699200000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((7499227321:ℚ)/10000000000),((7770499907:ℚ)/10000000000),((8395227321:ℚ)/25160000000),((25871499721:ℚ)/61000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1630274197:ℚ)/10000000000),((3941025844577951676514879401397562649893961695862523271503:ℚ)/485526545312500000000000000000000000000000000000000000000000),((-314346054698810426392462101:ℚ)/2957312000000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((386845091:ℚ)/500000000),((8008131927:ℚ)/10000000000),((143881697:ℚ)/432000000),((26584395781:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((9065747718280223750675311046287246733157605459462032160867:ℚ)/1133860123631250000000000000000000000000000000000000000000000),((-21873647:ℚ)/204800000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((1993641519:ℚ)/2500000000),((9908962189:ℚ)/10000000000),((2217641519:ℚ)/8000000000),((32286886567:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3483032687235223738728642861819297097503248745743623987:ℚ)/318864600000000000000000000000000000000000000000000000000),((-21873647:ℚ)/204800000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((9875599029:ℚ)/10000000000),((2741987317:ℚ)/2000000000),((10771599029:ℚ)/44160000000),((8737961951:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((7152773141817918656117699:ℚ)/487526400000000000000000000),((-21873647:ℚ)/204800000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound ninth nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC22
#check @N11Formalization.C450NinthGroupedC22.bound
#print axioms N11Formalization.C450NinthGroupedC22.valid0
#print axioms N11Formalization.C450NinthGroupedC22.valid1
#print axioms N11Formalization.C450NinthGroupedC22.valid2
#print axioms N11Formalization.C450NinthGroupedC22.valid3
#print axioms N11Formalization.C450NinthGroupedC22.valid4
#print axioms N11Formalization.C450NinthGroupedC22.valid5
#print axioms N11Formalization.C450NinthGroupedC22.valid6
#print axioms N11Formalization.C450NinthGroupedC22.valid7
#print axioms N11Formalization.C450NinthGroupedC22.valid8
#print axioms N11Formalization.C450NinthGroupedC22.valid9
#print axioms N11Formalization.C450NinthGroupedC22.valid10
#print axioms N11Formalization.C450NinthGroupedC22.valid11
#print axioms N11Formalization.C450NinthGroupedC22.valid12
#print axioms N11Formalization.C450NinthGroupedC22.valid13
#print axioms N11Formalization.C450NinthGroupedC22.valid14
#print axioms N11Formalization.C450NinthGroupedC22.valid15
#print axioms N11Formalization.C450NinthGroupedC22.bound
#print axioms N11Formalization.C450NinthGroupedC22.endpoint_checks
