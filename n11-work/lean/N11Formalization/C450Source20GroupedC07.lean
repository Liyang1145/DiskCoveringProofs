import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((6576355197:ℚ)/10000000000),((6885103843:ℚ)/10000000000),((-5733103843:ℚ)/9920000000),((-47027196773:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5250280261:ℚ)/10000000000),((7598715216501052503541393708783044388894665944693861269351:ℚ)/97091395276800000000000000000000000000000000000000000000000),((345680821889041229392780343:ℚ)/1108992000000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((6814916631:ℚ)/10000000000),((7004352119:ℚ)/10000000000),((-5852352119:ℚ)/10300000000),((-49174249679:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4585403387:ℚ)/10000000000),((70676626759224772484034237943690720710813709017106833847609:ℚ)/939404596505468750000000000000000000000000000000000000000000),((342527851464549171318316847:ℚ)/1108992000000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((3467084163:ℚ)/5000000000),((1765992377:ℚ)/2500000000),((-1477992377:ℚ)/2622500000),((-25123757467:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((263568393:ℚ)/625000000),((255406109699216699619796225808944228668926044313115904671:ℚ)/3460312871291845703125000000000000000000000000000000000000),((85233484081434949633527863:ℚ)/277248000000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((3496893689:ℚ)/5000000000),((3561791279:ℚ)/5000000000),((-2985791279:ℚ)/5292500000),((-25392043201:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((1005288353:ℚ)/2500000000),((928398092221529130873279960311042804138308509675480337:ℚ)/12566947003186035156250000000000000000000000000000000000),((28344384800764495608585989:ℚ)/92416000000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/8),((-9:ℚ)/16),((7053402061:ℚ)/10000000000),((3591595693:ℚ)/5000000000),((-3015595693:ℚ)/5340000000),((-51320618549:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3815751767:ℚ)/10000000000),((76591988943100958641584895449064783610391747579359488249:ℚ)/1035880415930566406250000000000000000000000000000000000000),((113109463394256739410256989:ℚ)/369664000000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((7113012493:ℚ)/10000000000),((1803248563:ℚ)/2500000000),((-1515248563:ℚ)/2693750000),((-3989008649:ℚ)/8325000000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((3599265481:ℚ)/10000000000),((31013672124760408774372882152129893644854673798963609613:ℚ)/423341036272001266479492187500000000000000000000000000000),((112840417699416711629022941:ℚ)/369664000000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((142856323:ℚ)/200000000),((7242796103:ℚ)/10000000000),((-6090796103:ℚ)/10822500000),((-1042506907:ℚ)/2174000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3486223039:ℚ)/10000000000),((3090505107436631672808734234239641359216633012385827092807:ℚ)/42166632075538623046875000000000000000000000000000000000000),((45082212420694070070461:ℚ)/147865600000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((3586309393:ℚ)/5000000000),((7302396817:ℚ)/10000000000),((-6150396817:ℚ)/10870000000),((-26196784537:ℚ)/54825000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3369553989:ℚ)/10000000000),((39707321205730130281768970082375103682714584904351774885607:ℚ)/536183464491080468750000000000000000000000000000000000000000),((28142600455457173041103541:ℚ)/92416000000000000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((904027631:ℚ)/1250000000),((230062301:ℚ)/312500000),((-194062301:ℚ)/342656250),((-6616248679:ℚ)/13825000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((624739183:ℚ)/2000000000),((17096221529305767197796064135352968190485816606249383031:ℚ)/230689330027922129631042480468750000000000000000000000000),((1754678366805568304176949:ℚ)/5776000000000000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7291819383:ℚ)/10000000000),((7421586647:ℚ)/10000000000),((-6269586647:ℚ)/11060000000),((-53466374447:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1428760571:ℚ)/5000000000),((13933746110049671388153895541540221994798792679051373887919:ℚ)/187886908459173437500000000000000000000000000000000000000000),((336082375157308058233861103:ℚ)/1108992000000000000000000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/8),((-9:ℚ)/16),((3675706947:ℚ)/5000000000),((7481175961:ℚ)/10000000000),((-6329175961:ℚ)/11155000000),((-27001362523:ℚ)/56250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1282352913:ℚ)/5000000000),((101849233261713045688391915471540369715167160250668239:ℚ)/1372472967027282714843750000000000000000000000000000000),((83815897706483949101884343:ℚ)/277248000000000000000000000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((7411004677:ℚ)/10000000000),((3800171927:ℚ)/5000000000),((-3224171927:ℚ)/5625000000),((-54539042093:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((111739793:ℚ)/500000000),((860248593102913602928215927218836693795482213492634294193:ℚ)/11373383331298828125000000000000000000000000000000000000000),((111480630892414928825416461:ℚ)/369664000000000000000000000)⟩
theorem valid11 : Valid source20 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-5:ℚ)/8),((-9:ℚ)/16),((3765087717:ℚ)/5000000000),((8076884637:ℚ)/10000000000),((-629534967:ℚ)/1040000000),((-27805789453:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((1356579941:ℚ)/10000000000),((1093518371683233958821261808612438762454911479557961297:ℚ)/13080059200000000000000000000000000000000000000000000000),((83197437984048246258188903:ℚ)/277248000000000000000000000)⟩
theorem valid12 : Valid source20 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source20 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((320269071:ℚ)/400000000),((8553243933:ℚ)/10000000000),((-7401243933:ℚ)/12200000000),((-2396021639:ℚ)/5184000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((3093082544540758412582769529574647309972367970946909772843:ℚ)/37230558525000000000000000000000000000000000000000000000000),((38298271:ℚ)/128000000)⟩
theorem valid13 : Valid source20 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((8483095379:ℚ)/10000000000),((10457385739:ℚ)/10000000000),((-9305385739:ℚ)/12960000000),((-64187858411:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2216741131070876245128590091872696808883175193331714783:ℚ)/20407334400000000000000000000000000000000000000000000000),((38298271:ℚ)/128000000)⟩
theorem valid14 : Valid source20 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((5193632761:ℚ)/5000000000),((14262241387:ℚ)/10000000000),((-13110241387:ℚ)/16000000000),((-40662694849:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2079846180154810679132531980397768407075736096086544008037:ℚ)/15235200000000000000000000000000000000000000000000000000000),((38298271:ℚ)/128000000)⟩
theorem valid15 : Valid source20 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source20 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((4329:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source20 nn0 nn1 Qcell ((4329:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source20 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source20 nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source20 nn0 nn1 Qcell ((2193:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source20 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC07
#check @N11Formalization.C450Source20GroupedC07.bound
#print axioms N11Formalization.C450Source20GroupedC07.valid0
#print axioms N11Formalization.C450Source20GroupedC07.valid1
#print axioms N11Formalization.C450Source20GroupedC07.valid2
#print axioms N11Formalization.C450Source20GroupedC07.valid3
#print axioms N11Formalization.C450Source20GroupedC07.valid4
#print axioms N11Formalization.C450Source20GroupedC07.valid5
#print axioms N11Formalization.C450Source20GroupedC07.valid6
#print axioms N11Formalization.C450Source20GroupedC07.valid7
#print axioms N11Formalization.C450Source20GroupedC07.valid8
#print axioms N11Formalization.C450Source20GroupedC07.valid9
#print axioms N11Formalization.C450Source20GroupedC07.valid10
#print axioms N11Formalization.C450Source20GroupedC07.valid11
#print axioms N11Formalization.C450Source20GroupedC07.valid12
#print axioms N11Formalization.C450Source20GroupedC07.valid13
#print axioms N11Formalization.C450Source20GroupedC07.valid14
#print axioms N11Formalization.C450Source20GroupedC07.valid15
#print axioms N11Formalization.C450Source20GroupedC07.bound
#print axioms N11Formalization.C450Source20GroupedC07.endpoint_checks
