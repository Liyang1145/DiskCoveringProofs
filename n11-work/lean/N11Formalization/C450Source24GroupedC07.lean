import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((6652160463:ℚ)/10000000000),((6852804281:ℚ)/10000000000),((-5444804281:ℚ)/9920000000),((-45149444167:ℚ)/101100000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((50477301:ℚ)/100000000),((66646834405210988781540914951339148866648007884390703272719:ℚ)/300321508696875000000000000000000000000000000000000000000000),((12344975707339825341073177:ℚ)/44359680000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((3385860501:ℚ)/5000000000),((348615719:ℚ)/500000000),((-92738573:ℚ)/168500000),((-23112744509:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((4712181989:ℚ)/10000000000),((105595928547808411855293050982618946056592141848613211:ℚ)/475823011613671875000000000000000000000000000000000000),((3052178721979294808794033:ℚ)/11089920000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((6891251341:ℚ)/10000000000),((219751841:ℚ)/312500000),((-175751841:ℚ)/321875000),((-47301262069:ℚ)/103950000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((4352999549:ℚ)/10000000000),((24589849507480715524734014245890884341950449570770537069:ℚ)/112605796842741966247558593750000000000000000000000000000),((11145973294431927502931:ℚ)/40960000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((695100571:ℚ)/1000000000),((709179669:ℚ)/1000000000),((-51670879:ℚ)/94500000),((-4783905139:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((2081319297:ℚ)/5000000000),((22640755573944831444559642330354370459170011649300037:ℚ)/103642622194042968750000000000000000000000000000000000),((40005880075861459703451:ℚ)/147865600000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((876344143:ℚ)/1250000000),((7151527897:ℚ)/10000000000),((-5743527897:ℚ)/10490000000),((-6047097287:ℚ)/13231250000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1981862851:ℚ)/5000000000),((48394731565865318466646096169163277851188641778045869161181:ℚ)/221460023762678125000000000000000000000000000000000000000000),((62146340586695050981939:ℚ)/231040000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((707049383:ℚ)/1000000000),((1795347773:ℚ)/2500000000),((-1443347773:ℚ)/2646250000),((-4891444447:ℚ)/10632500000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((3754897307:ℚ)/10000000000),((227121847025135161550168811481424028536318384468069713239577:ℚ)/1047450238998806866455078125000000000000000000000000000000000),((39540296965268467060579:ℚ)/147865600000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((71003617:ℚ)/100000000),((721125271:ℚ)/1000000000),((-580325271:ℚ)/1063250000),((-491832553:ℚ)/1068000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((455779263:ℚ)/1250000000),((14518912845072381073002469229333258451566512331221610771:ℚ)/66945089612122229003906250000000000000000000000000000000),((394231892666178906579:ℚ)/1478656000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((7130227951:ℚ)/10000000000),((7241112773:ℚ)/10000000000),((-5833112773:ℚ)/10680000000),((-49452051559:ℚ)/107275000000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((706878269:ℚ)/2000000000),((237576874563483981287655703580746287026245628532116978996233:ℚ)/1095218660690634375000000000000000000000000000000000000000000),((3930579671982035079559411:ℚ)/14786560000000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-5:ℚ)/8),((-9:ℚ)/16),((1432018521:ℚ)/2000000000),((3635485651:ℚ)/5000000000),((-2931485651:ℚ)/5363750000),((-9944166689:ℚ)/21550000000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((683811279:ℚ)/2000000000),((260299180060600613232285546096518644084971804562237983823:ℚ)/1199729619371070671081542968750000000000000000000000000000),((470257431425222442816553:ℚ)/1774387200000000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((1797488921:ℚ)/2500000000),((1832670959:ℚ)/2500000000),((-1480670959:ℚ)/2693750000),((-12497400289:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((412482807:ℚ)/1250000000),((15786783883844527860819195810249419376293613795015838326099:ℚ)/72174032755187225341796875000000000000000000000000000000000),((244188480769758457383651:ℚ)/924160000000000000000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((1812419299:ℚ)/2500000000),((7390390473:ℚ)/10000000000),((-5982390473:ℚ)/10870000000),((-12631773691:ℚ)/27412500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((762017477:ℚ)/2500000000),((117314021225582913102661500112806153137512931521385201561053:ℚ)/536183464491080468750000000000000000000000000000000000000000),((242708608032574242482411:ℚ)/924160000000000000000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((7309392653:ℚ)/10000000000),((3725045683:ℚ)/5000000000),((-3021045683:ℚ)/5482500000),((-7294933411:ℚ)/15800000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1387155597:ℚ)/5000000000),((1669431278711818076311254136529160913168866521280320231:ℚ)/7628063612393188476562500000000000000000000000000000000),((3859545750682446132415499:ℚ)/14786560000000000000000000)⟩
theorem valid11 : Valid source24 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source24 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-5:ℚ)/8),((-9:ℚ)/16),((1842275553:ℚ)/2500000000),((3784738253:ℚ)/5000000000),((-3080738253:ℚ)/5530000000),((-12900479977:ℚ)/28125000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2471290501:ℚ)/10000000000),((5308519188143387241953161912813543206428885669990879:ℚ)/23887595104980468750000000000000000000000000000000000),((719182449599855172600697:ℚ)/2772480000000000000000000)⟩
theorem valid12 : Valid source24 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source24 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((3744252119:ℚ)/5000000000),((3844420193:ℚ)/5000000000),((-348935577:ℚ)/625000000),((-26338269071:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1715022251:ℚ)/10000000000),((3467606861091306333760667975197120451111429913401257933:ℚ)/15601348876953125000000000000000000000000000000000000000),((2622912369318180676811:ℚ)/10240000000000000000000)⟩
theorem valid13 : Valid source24 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((3803942217:ℚ)/5000000000),((8643099221:ℚ)/10000000000),((-7235099221:ℚ)/11440000000),((-26875479953:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((208547197289706870172420963468281445923347270720030102191:ℚ)/787106548800000000000000000000000000000000000000000000000),((32393521:ℚ)/128000000)⟩
theorem valid14 : Valid source24 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((4281128173:ℚ)/5000000000),((10549177913:ℚ)/10000000000),((-9141177913:ℚ)/12960000000),((-31170153557:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((6125778328591712291807025933602830429320197846478890599:ℚ)/20407334400000000000000000000000000000000000000000000000),((32393521:ℚ)/128000000)⟩
theorem valid15 : Valid source24 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((83747969:ℚ)/80000000),((1794537479:ℚ)/1250000000),((-1618537479:ℚ)/2000000000),((-635971721:ℚ)/1766400000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((10866060752883792614729239816180822604602506286296643811:ℚ)/29756250000000000000000000000000000000000000000000000000),((32393521:ℚ)/128000000)⟩
theorem valid16 : Valid source24 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source24 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4253:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source24 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source24 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4291:ℚ)/6400) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((4291:ℚ)/6400) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source24 nn0 nn1 Qcell ((4291:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source24 nn0 nn1 Qcell ((4291:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source24 nn0 nn1 Qcell ((4291:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC07
#check @N11Formalization.C450Source24GroupedC07.bound
#print axioms N11Formalization.C450Source24GroupedC07.valid0
#print axioms N11Formalization.C450Source24GroupedC07.valid1
#print axioms N11Formalization.C450Source24GroupedC07.valid2
#print axioms N11Formalization.C450Source24GroupedC07.valid3
#print axioms N11Formalization.C450Source24GroupedC07.valid4
#print axioms N11Formalization.C450Source24GroupedC07.valid5
#print axioms N11Formalization.C450Source24GroupedC07.valid6
#print axioms N11Formalization.C450Source24GroupedC07.valid7
#print axioms N11Formalization.C450Source24GroupedC07.valid8
#print axioms N11Formalization.C450Source24GroupedC07.valid9
#print axioms N11Formalization.C450Source24GroupedC07.valid10
#print axioms N11Formalization.C450Source24GroupedC07.valid11
#print axioms N11Formalization.C450Source24GroupedC07.valid12
#print axioms N11Formalization.C450Source24GroupedC07.valid13
#print axioms N11Formalization.C450Source24GroupedC07.valid14
#print axioms N11Formalization.C450Source24GroupedC07.valid15
#print axioms N11Formalization.C450Source24GroupedC07.valid16
#print axioms N11Formalization.C450Source24GroupedC07.bound
#print axioms N11Formalization.C450Source24GroupedC07.endpoint_checks
