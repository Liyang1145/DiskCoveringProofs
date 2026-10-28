import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((6698071589:ℚ)/10000000000),((691537071:ℚ)/1000000000),((-4367833639:ℚ)/9920000000),((-4298071589:ℚ)/12637500000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4921368057:ℚ)/10000000000),((22234636128109218079512341945340483301133:ℚ)/83148818325504000000000000000000000000000),((3640328855782615696003827139:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((6818381323:ℚ)/10000000000),((7035584193:ℚ)/10000000000),((-44760257737:ℚ)/101100000000),((-4418381323:ℚ)/12875000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((915018697:ℚ)/2000000000),((127223072857575858949642663634552081413138724025530405643859:ℚ)/475823011613671875000000000000000000000000000000000000000000),((3547069817681720527962072611:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((6938632417:ℚ)/10000000000),((709567051:ℚ)/1000000000),((-4530103459:ℚ)/10300000000),((-412602947:ℚ)/1181250000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((1050680283:ℚ)/2500000000),((84099129995498886628394616291278680829236267141394485811:ℚ)/317653818090820312500000000000000000000000000000000000000),((3452704358564554871341982651:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((1399747401:ℚ)/2000000000),((1431148743:ℚ)/2000000000),((-9168338687:ℚ)/20790000000),((-919747401:ℚ)/2622500000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((1001119963:ℚ)/2500000000),((124941241870304089351945575764832544575070200181451780797:ℚ)/471845071293750000000000000000000000000000000000000000000),((136204257147787233877054059:ℚ)/591462400000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7058828137:ℚ)/10000000000),((7215804169:ℚ)/10000000000),((-46382237521:ℚ)/104900000000),((-4658828137:ℚ)/13231250000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((59320829:ℚ)/156250000),((117303896307016292212853951918245181877094907258441295599289691:ℚ)/442920047525356250000000000000000000000000000000000000000000000),((3357231553293635943161590571:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((3559453093:ℚ)/5000000000),((363792611:ℚ)/500000000),((-2346133499:ℚ)/5292500000),((-2359453093:ℚ)/6675000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((143087307:ℚ)/400000000),((486028594719935641257591014986368945130315087276604699657:ℚ)/1834774262465161132812500000000000000000000000000000000000),((827269906424195498218871491:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((1794742877:ℚ)/2500000000),((1467177641:ℚ)/2000000000),((-9492598769:ℚ)/21360000000),((-1194742877:ℚ)/3367187500),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1672089683:ℚ)/5000000000),((333102652817103434179364747957753965193266148099886617162843:ℚ)/1257175165526400000000000000000000000000000000000000000000000),((203790659112913487504913811:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((7239024449:ℚ)/10000000000),((1479182489:ℚ)/2000000000),((-9600642401:ℚ)/21550000000),((-4839024449:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((773608509:ℚ)/2500000000),((19587411473845530760063369685652598647125772023937413931935723:ℚ)/73906209541311718750000000000000000000000000000000000000000000),((3211944214808979220976523259:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((7299065339:ℚ)/10000000000),((1878981733:ℚ)/2500000000),((-12270835597:ℚ)/27175000000),((-699866477:ℚ)/1975000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2823500553:ℚ)/10000000000),((13090541946072428469225054781748578078546133919855506973991:ℚ)/48924103419329833984375000000000000000000000000000000000000),((3162960540325070875473627139:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((7419112239:ℚ)/10000000000),((7755827991:ℚ)/10000000000),((-51242451919:ℚ)/110600000000),((-5019112239:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((546534993:ℚ)/2500000000),((10565573479724507685208182520772955889024423385177591513503:ℚ)/38777517350000000000000000000000000000000000000000000000000),((3064160798557526053092270939:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((1914768699:ℚ)/2500000000),((8714006471:ℚ)/10000000000),((-4605081403:ℚ)/8800000000),((-48695137:ℚ)/150000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((20563714382015221321417106496613:ℚ)/68750000000000000000000000000000),((201739673:ℚ)/1024000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((2154365571:ℚ)/2500000000),((1328207441:ℚ)/1250000000),((-9633866969:ℚ)/16200000000),((-1554365571:ℚ)/5000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((830082166649651917150540198855966181:ℚ)/2531250000000000000000000000000000000),((201739673:ℚ)/1024000000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((263235301:ℚ)/250000000),((14439288033:ℚ)/10000000000),((-111393592297:ℚ)/160000000000),((-203235301:ℚ)/690000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((30507980387680756142447:ℚ)/79350000000000000000000),((201739673:ℚ)/1024000000)⟩
theorem valid12 : Valid source31 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source31 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2079:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source31 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source31 nn0 nn1 Qcell ((2079:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source31 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC08
#check @N11Formalization.C450Source31GroupedC08.bound
#print axioms N11Formalization.C450Source31GroupedC08.valid0
#print axioms N11Formalization.C450Source31GroupedC08.valid1
#print axioms N11Formalization.C450Source31GroupedC08.valid2
#print axioms N11Formalization.C450Source31GroupedC08.valid3
#print axioms N11Formalization.C450Source31GroupedC08.valid4
#print axioms N11Formalization.C450Source31GroupedC08.valid5
#print axioms N11Formalization.C450Source31GroupedC08.valid6
#print axioms N11Formalization.C450Source31GroupedC08.valid7
#print axioms N11Formalization.C450Source31GroupedC08.valid8
#print axioms N11Formalization.C450Source31GroupedC08.valid9
#print axioms N11Formalization.C450Source31GroupedC08.valid10
#print axioms N11Formalization.C450Source31GroupedC08.valid11
#print axioms N11Formalization.C450Source31GroupedC08.valid12
#print axioms N11Formalization.C450Source31GroupedC08.bound
#print axioms N11Formalization.C450Source31GroupedC08.endpoint_checks
