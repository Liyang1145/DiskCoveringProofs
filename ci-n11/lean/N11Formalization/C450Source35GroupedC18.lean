import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/16),((1:ℚ)/8),((1470347067:ℚ)/2500000000),((3109377419:ℚ)/5000000000),((6750347067:ℚ)/25750000000),((8549377419:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1714680729:ℚ)/2500000000),((-22944602885711887242271107765812187062829283462728814690947:ℚ)/102549867871093750000000000000000000000000000000000000000000),((-7469337724132822316733713:ℚ)/28880000000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((6124498091:ℚ)/10000000000),((6340024453:ℚ)/10000000000),((27244498091:ℚ)/104900000000),((17220024453:ℚ)/51500000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((6336782729:ℚ)/10000000000),((-4231553068982895242396325256511845486672120666902729096469259:ℚ)/19134668383189062500000000000000000000000000000000000000000000),((-30794731730259590369995697:ℚ)/115520000000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((6245895419:ℚ)/10000000000),((129224033:ℚ)/200000000),((307481971:ℚ)/1200000000),((346824033:ℚ)/1049000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((757729479:ℚ)/1250000000),((-71846590173963080620789368661376324393144293450450692371:ℚ)/330120300000000000000000000000000000000000000000000000000),((-12460088048070670605737:ℚ)/46208000000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((6367195497:ℚ)/10000000000),((6582291471:ℚ)/10000000000),((27487195497:ℚ)/108700000000),((17462291471:ℚ)/53400000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((46206039:ℚ)/80000000),((-40880404863273726572363313275677537493341882382778362618955251:ℚ)/190752359048681250000000000000000000000000000000000000000000000),((-31501600769147633122784953:ℚ)/115520000000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((1:ℚ)/16),((1:ℚ)/8),((162210091:ℚ)/250000000),((664280509:ℚ)/1000000000),((690210091:ℚ)/2741250000),((1752280509:ℚ)/5435000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((5476752759:ℚ)/10000000000),((-900939652608624764371135556779418629697214981660740069059:ℚ)/4225543129128836059570312500000000000000000000000000000000),((-319536658754686860155873:ℚ)/1155200000000000000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((654897479:ℚ)/1000000000),((209478081:ℚ)/312500000),((2766897479:ℚ)/11060000000),((549478081:ℚ)/1713281250),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((532171623:ℚ)/1000000000),((-14942287252850799424376149408939528464245083345563596164799:ℚ)/70599264754763281250000000000000000000000000000000000000000),((-250989889700195391946829:ℚ)/902500000000000000000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((3304762389:ℚ)/5000000000),((3412113681:ℚ)/5000000000),((4621587463:ℚ)/18750000000),((8852113681:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5162541757:ℚ)/10000000000),((-6175099577084790573000213326211246191241740960479171093:ℚ)/29665231704711914062500000000000000000000000000000000000),((-8048033746138302065724313:ℚ)/28880000000000000000000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((3365281747:ℚ)/5000000000),((6945081823:ℚ)/10000000000),((1071175519:ℚ)/4400000000),((1980564647:ℚ)/6250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4830110589:ℚ)/10000000000),((-109308743028553968247090626631719686322923950029796591:ℚ)/532400000000000000000000000000000000000000000000000000),((-32531332362698608263005657:ℚ)/115520000000000000000000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((6851524049:ℚ)/10000000000),((7065865747:ℚ)/10000000000),((27971524049:ℚ)/116300000000),((17945865747:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1118838849:ℚ)/2500000000),((-40733054029720925778136945022038280386978009140238340680085921:ℚ)/201044055552518750000000000000000000000000000000000000000000000),((-32866509909602704827076097:ℚ)/115520000000000000000000000)⟩
theorem valid8 : Valid source35 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((3486205207:ℚ)/5000000000),((898322831:ℚ)/1250000000),((14046205207:ℚ)/59100000000),((2258322831:ℚ)/7268750000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4092427097:ℚ)/10000000000),((-9696252664738031186052093390452147830679986430376848219721247:ℚ)/48472943030798437500000000000000000000000000000000000000000000),((-27300728550525521287577:ℚ)/95000000000000000000000)⟩
theorem valid9 : Valid source35 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source35 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((1418645259:ℚ)/2000000000),((1856957077:ℚ)/2500000000),((5642645259:ℚ)/24400000000),((1525652359:ℚ)/4925000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((459059061:ℚ)/1250000000),((-684926735320072382505591223511650641705152752615147561300899:ℚ)/3523562251600000000000000000000000000000000000000000000000000),((-109520689200762353434103:ℚ)/380000000000000000000000)⟩
theorem valid10 : Valid source35 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source35 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((916832527:ℚ)/1250000000),((3954823269:ℚ)/5000000000),((3556832527:ℚ)/16200000000),((9394823269:ℚ)/30500000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((2650214967:ℚ)/10000000000),((-675801999564360805606688934045188589464661666453387356221:ℚ)/3662022150000000000000000000000000000000000000000000000000),((-358588042070683:ℚ)/1216000000000000)⟩
theorem valid11 : Valid source35 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((7816820391:ℚ)/10000000000),((2457585119:ℚ)/2500000000),((28936820391:ℚ)/160000000000),((5177585119:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-2899430629368759481598529608949384182332549784884998291868751:ℚ)/18662400000000000000000000000000000000000000000000000000000000),((-9773639:ℚ)/32000000)⟩
theorem valid12 : Valid source35 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((9738546813:ℚ)/10000000000),((170680903:ℚ)/125000000),((10286182271:ℚ)/73600000000),((306680903:ℚ)/1000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-78865735061318095189461999680599098987603340322122226999:ℚ)/622950400000000000000000000000000000000000000000000000000),((-9773639:ℚ)/32000000)⟩
theorem valid13 : Valid source35 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source35 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC18
#check @N11Formalization.C450Source35GroupedC18.bound
#print axioms N11Formalization.C450Source35GroupedC18.valid0
#print axioms N11Formalization.C450Source35GroupedC18.valid1
#print axioms N11Formalization.C450Source35GroupedC18.valid2
#print axioms N11Formalization.C450Source35GroupedC18.valid3
#print axioms N11Formalization.C450Source35GroupedC18.valid4
#print axioms N11Formalization.C450Source35GroupedC18.valid5
#print axioms N11Formalization.C450Source35GroupedC18.valid6
#print axioms N11Formalization.C450Source35GroupedC18.valid7
#print axioms N11Formalization.C450Source35GroupedC18.valid8
#print axioms N11Formalization.C450Source35GroupedC18.valid9
#print axioms N11Formalization.C450Source35GroupedC18.valid10
#print axioms N11Formalization.C450Source35GroupedC18.valid11
#print axioms N11Formalization.C450Source35GroupedC18.valid12
#print axioms N11Formalization.C450Source35GroupedC18.valid13
#print axioms N11Formalization.C450Source35GroupedC18.bound
#print axioms N11Formalization.C450Source35GroupedC18.endpoint_checks
