import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((6595575569:ℚ)/10000000000),((431696071:ℚ)/625000000),((-355696071:ℚ)/620000000),((-46560180121:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2599801647:ℚ)/5000000000),((1718761587045532972341196401217826672395553972562998831:ℚ)/15802635950000000000000000000000000000000000000000000000),((113049879108836017308621661:ℚ)/369664000000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((1708564781:ℚ)/2500000000),((7026439619:ℚ)/10000000000),((-5810439619:ℚ)/10300000000),((-12177083029:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((905513361:ℚ)/2000000000),((196593570746229732410290463462591572261983368770815997183419:ℚ)/1878809193010937500000000000000000000000000000000000000000000),((6984155032641865034905861:ℚ)/23104000000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((1738392129:ℚ)/2500000000),((7086083371:ℚ)/10000000000),((-5870083371:ℚ)/10490000000),((-12445529161:ℚ)/26462500000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1038572761:ℚ)/2500000000),((45484922950528416724313588602012700794659957967426504859387:ℚ)/442920047525356250000000000000000000000000000000000000000000),((20828840963703151634397623:ℚ)/69312000000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((701321563:ℚ)/1000000000),((7145722311:ℚ)/10000000000),((-5929722311:ℚ)/10585000000),((-5031894067:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((1977662409:ℚ)/5000000000),((20665658657921785712140449953153543904835765579972491943:ℚ)/201071152050976562500000000000000000000000000000000000000),((1107555784637841075462069:ℚ)/3696640000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/8),((-9:ℚ)/16),((707285787:ℚ)/1000000000),((3602678283:ℚ)/5000000000),((-2994678283:ℚ)/5340000000),((-5085572083:ℚ)/10775000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3746406187:ℚ)/10000000000),((71032542516040099085488478081672063678668425736219539323:ℚ)/690586943953710937500000000000000000000000000000000000000),((3312681956858882503605407:ℚ)/11089920000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((3566247683:ℚ)/5000000000),((363249313:ℚ)/500000000),((-302449313:ℚ)/538750000),((-25696229147:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3525761739:ℚ)/10000000000),((118867258533220720312763791354475705489328718148788241377:ℚ)/1154784524082995605468750000000000000000000000000000000000),((27522152922496025598695589:ℚ)/92416000000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((1798032061:ℚ)/2500000000),((7324611513:ℚ)/10000000000),((-6108611513:ℚ)/10870000000),((-12982288549:ℚ)/27412500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((205689309:ℚ)/625000000),((110461359431185171763496708236583868060225984990063939433553:ℚ)/1072366928982160937500000000000000000000000000000000000000000),((6859576090503724076099621:ℚ)/23104000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((58014053:ℚ)/80000000),((184605811:ℚ)/250000000),((-51401937:ℚ)/91375000),((-419726477:ℚ)/884800000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3038939671:ℚ)/10000000000),((85887706978146108469399369867911449515082646393291181:ℚ)/833248232622900390625000000000000000000000000000000000),((7002659122368586521909:ℚ)/23658496000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((11698209:ℚ)/16000000),((116310143:ℚ)/156250000),((-13901449:ℚ)/24687500),((-84803881:ℚ)/178480000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((552948921:ℚ)/2000000000),((96554213942914112869471666781318471730823306473030373:ℚ)/936139331847763061523437500000000000000000000000000000),((837723689027647818743:ℚ)/2839019520000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/8),((-9:ℚ)/16),((7371000359:ℚ)/10000000000),((3751730879:ℚ)/5000000000),((-3143730879:ℚ)/5577500000),((-53539003231:ℚ)/112500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1230529921:ℚ)/5000000000),((141642533191873958901223544866076861923200476054671549:ℚ)/1372472967027282714843750000000000000000000000000000000),((108739386744332380249644781:ℚ)/369664000000000000000000000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((7430615933:ℚ)/10000000000),((3811337531:ℚ)/5000000000),((-1067779177:ℚ)/1875000000),((-54075543397:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((423042889:ℚ)/2000000000),((29525562562491846572590222201815008413171702422068324771:ℚ)/280824279785156250000000000000000000000000000000000000000),((108398892665913209678087589:ℚ)/369664000000000000000000000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-5:ℚ)/8),((-9:ℚ)/16),((301993401:ℚ)/400000000),((8099383201:ℚ)/10000000000),((-6883383201:ℚ)/11440000000),((-2205940609:ℚ)/4880000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((1149602443:ℚ)/10000000000),((4037469208235060485237387601902836171323699539107001642329:ℚ)/34819117590400000000000000000000000000000000000000000000000),((517027568209343372452103:ℚ)/1774387200000000000000000)⟩
theorem valid11 : Valid source21 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((501660281:ℚ)/625000000),((4287945023:ℚ)/5000000000),((-3679945023:ℚ)/6100000000),((-3714942529:ℚ)/8100000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1072547166428707149708703266526899397389810156229304788783:ℚ)/9307639631250000000000000000000000000000000000000000000000),((37196803:ℚ)/128000000)⟩
theorem valid12 : Valid source21 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((4251545073:ℚ)/5000000000),((10480480953:ℚ)/10000000000),((-9264480953:ℚ)/12960000000),((-31863905657:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2040440299660989339292474675727862662526325149777552433:ℚ)/13604889600000000000000000000000000000000000000000000000),((37196803:ℚ)/128000000)⟩
theorem valid13 : Valid source21 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((2601934571:ℚ)/2500000000),((7142931163:ℚ)/5000000000),((-6534931163:ℚ)/8000000000),((-20217411139:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((716267220115727882122871051583547616603277960038721114283:ℚ)/3808800000000000000000000000000000000000000000000000000000),((37196803:ℚ)/128000000)⟩
theorem valid14 : Valid source21 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source21 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source21 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source21 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source21 nn0 nn1 Qcell ((2117:ℚ)/3200) ((2193:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source21 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source21 nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source21 nn0 nn1 Qcell ((2193:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source21 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC07
#check @N11Formalization.C450Source21GroupedC07.bound
#print axioms N11Formalization.C450Source21GroupedC07.valid0
#print axioms N11Formalization.C450Source21GroupedC07.valid1
#print axioms N11Formalization.C450Source21GroupedC07.valid2
#print axioms N11Formalization.C450Source21GroupedC07.valid3
#print axioms N11Formalization.C450Source21GroupedC07.valid4
#print axioms N11Formalization.C450Source21GroupedC07.valid5
#print axioms N11Formalization.C450Source21GroupedC07.valid6
#print axioms N11Formalization.C450Source21GroupedC07.valid7
#print axioms N11Formalization.C450Source21GroupedC07.valid8
#print axioms N11Formalization.C450Source21GroupedC07.valid9
#print axioms N11Formalization.C450Source21GroupedC07.valid10
#print axioms N11Formalization.C450Source21GroupedC07.valid11
#print axioms N11Formalization.C450Source21GroupedC07.valid12
#print axioms N11Formalization.C450Source21GroupedC07.valid13
#print axioms N11Formalization.C450Source21GroupedC07.valid14
#print axioms N11Formalization.C450Source21GroupedC07.bound
#print axioms N11Formalization.C450Source21GroupedC07.endpoint_checks
