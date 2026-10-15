import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((3307308387:ℚ)/5000000000),((866127101:ℚ)/1250000000),((-706127101:ℚ)/1240000000),((-23045775483:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2574476233:ℚ)/5000000000),((954076876548567529106440960061170594676309872268397239:ℚ)/6117149400000000000000000000000000000000000000000000000),((40357025925363212697764903:ℚ)/138624000000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((1370685851:ℚ)/2000000000),((7048376357:ℚ)/10000000000),((-5768376357:ℚ)/10300000000),((-9648172659:ℚ)/20980000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2234779497:ℚ)/5000000000),((141400391215713332810580026307124682481898865034857192448659:ℚ)/939404596505468750000000000000000000000000000000000000000000),((2118942507339829655364829:ℚ)/7393280000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((1394559911:ℚ)/2000000000),((888505983:ℚ)/1250000000),((-728505983:ℚ)/1311250000),((-9863039199:ℚ)/21170000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((127848129:ℚ)/312500000),((63994400042876340007639864927404909216996069085249214297:ℚ)/432539108911480712890625000000000000000000000000000000000),((2102002879891967953402709:ℚ)/7393280000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((703247629:ℚ)/1000000000),((895964257:ℚ)/1250000000),((-735964257:ℚ)/1323125000),((-1661742887:ℚ)/3560000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((1944511603:ℚ)/5000000000),((464993922125457381227594681739884830408912150042803177:ℚ)/3141736750796508789062500000000000000000000000000000000),((523369285973650098180589:ℚ)/1848320000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/8),((-9:ℚ)/16),((7092147617:ℚ)/10000000000),((7227375077:ℚ)/10000000000),((-1982458359:ℚ)/3560000000),((-50389328553:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3676423453:ℚ)/10000000000),((15147602956965816572885908425606250736015126791559215713:ℚ)/102309176882031250000000000000000000000000000000000000000),((52122852791166828599818981:ℚ)/184832000000000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((89397671:ℚ)/125000000),((7287031063:ℚ)/10000000000),((-6007031063:ℚ)/10775000000),((-636579039:ℚ)/1358750000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3451399413:ℚ)/10000000000),((684121700280210278368804787615379828714511935944404813122761:ℚ)/4619138096331982421875000000000000000000000000000000000000000),((8110600674593649455989:ℚ)/28880000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7211474619:ℚ)/10000000000),((3673341073:ℚ)/5000000000),((-3033341073:ℚ)/5435000000),((-17154423857:ℚ)/36550000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((12845341:ℚ)/40000000),((9929571437165464744171198499821469335531441725080998009719:ℚ)/67022933061385058593750000000000000000000000000000000000000),((155075708760176519844418007:ℚ)/554496000000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((908891321:ℚ)/1250000000),((7406328453:ℚ)/10000000000),((-6126328453:ℚ)/10965000000),((-6500021889:ℚ)/13825000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((184534947:ℚ)/625000000),((1250267676154227399630207858782456727545274502813820760311:ℚ)/8436638355306866455078125000000000000000000000000000000000),((804297318063292952479189:ℚ)/2888000000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-5:ℚ)/8),((-9:ℚ)/16),((7330781657:ℚ)/10000000000),((7525607231:ℚ)/10000000000),((-6245607231:ℚ)/11060000000),((-17512344971:ℚ)/37500000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2669629247:ℚ)/10000000000),((22396568102751913090676323768093963039042933887632353:ℚ)/148633925097656250000000000000000000000000000000000000),((51257220388351290887220821:ℚ)/184832000000000000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((931258719:ℚ)/1250000000),((764486833:ℚ)/1000000000),((-636486833:ℚ)/1125000000),((-6701328471:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((994808301:ℚ)/5000000000),((13711941001905515813226199482259172527349670904560434551:ℚ)/90987066650390625000000000000000000000000000000000000000),((2382131406428153825962607:ℚ)/8664000000000000000000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-5:ℚ)/8),((-9:ℚ)/16),((1513867971:ℚ)/2000000000),((4060876299:ℚ)/5000000000),((-3420876299:ℚ)/5720000000),((-10936811739:ℚ)/24400000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((898548279:ℚ)/10000000000),((17597471535574892209311993246637524747236898076737072619:ℚ)/107025976200000000000000000000000000000000000000000000000),((6045198004512710348904167:ℚ)/22179840000000000000000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((80462573:ℚ)/100000000),((2149603677:ℚ)/2500000000),((-1829603677:ℚ)/3050000000),((-196587719:ℚ)/432000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((10558004709839119999399069546850394857308459226039210659:ℚ)/64636386328125000000000000000000000000000000000000000000),((17403869:ℚ)/64000000)⟩
theorem valid11 : Valid source22 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((8522948653:ℚ)/10000000000),((10503478093:ℚ)/10000000000),((-9223478093:ℚ)/12960000000),((-63266537877:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((4234475996200840988467400747152756824090220174971105337:ℚ)/20407334400000000000000000000000000000000000000000000000),((17403869:ℚ)/64000000)⟩
theorem valid12 : Valid source22 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((10428101019:ℚ)/10000000000),((2861882479:ℚ)/2000000000),((-2605882479:ℚ)/3200000000),((-26804303057:ℚ)/73600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((3454717691581249560792432082284910342278280746844656817:ℚ)/13542400000000000000000000000000000000000000000000000000),((17403869:ℚ)/64000000)⟩
theorem valid13 : Valid source22 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source22 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source22 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source22 nn0 nn1 Qcell ((2117:ℚ)/3200) ((2193:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source22 nn0 nn1 Qcell ((2193:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source22 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC07
#check @N11Formalization.C450Source22GroupedC07.bound
#print axioms N11Formalization.C450Source22GroupedC07.valid0
#print axioms N11Formalization.C450Source22GroupedC07.valid1
#print axioms N11Formalization.C450Source22GroupedC07.valid2
#print axioms N11Formalization.C450Source22GroupedC07.valid3
#print axioms N11Formalization.C450Source22GroupedC07.valid4
#print axioms N11Formalization.C450Source22GroupedC07.valid5
#print axioms N11Formalization.C450Source22GroupedC07.valid6
#print axioms N11Formalization.C450Source22GroupedC07.valid7
#print axioms N11Formalization.C450Source22GroupedC07.valid8
#print axioms N11Formalization.C450Source22GroupedC07.valid9
#print axioms N11Formalization.C450Source22GroupedC07.valid10
#print axioms N11Formalization.C450Source22GroupedC07.valid11
#print axioms N11Formalization.C450Source22GroupedC07.valid12
#print axioms N11Formalization.C450Source22GroupedC07.valid13
#print axioms N11Formalization.C450Source22GroupedC07.bound
#print axioms N11Formalization.C450Source22GroupedC07.endpoint_checks
