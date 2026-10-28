import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((6646549641:ℚ)/10000000000),((3420993547:ℚ)/5000000000),((-31550929017:ℚ)/49600000000),((-5366549641:ℚ)/10110000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((1012594969:ℚ)/2000000000),((82612675690303953144803084826067573565434186210439529899504273:ℚ)/779520171801600000000000000000000000000000000000000000000000000),((17087919166925434894091261821:ℚ)/44359680000000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((845729589:ℚ)/1250000000),((6961232821:ℚ)/10000000000),((-64413561031:ℚ)/101100000000),((-685729589:ℚ)/1287500000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((4729208533:ℚ)/10000000000),((7272861725010268040223261910711151693993721393212958984939311:ℚ)/68518513672368750000000000000000000000000000000000000000000000),((266365204602149726790611461:ℚ)/693120000000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((3442551919:ℚ)/5000000000),((7020848847:ℚ)/10000000000),((-631741139:ℚ)/1000000000),((-934183973:ℚ)/1732500000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((2186071209:ℚ)/5000000000),((11104511780425211021901405447969490874203328211487602277:ℚ)/107198437500000000000000000000000000000000000000000000000),((1417192006741327266846139567:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((6944730267:ℚ)/10000000000),((7080460481:ℚ)/10000000000),((-21908355097:ℚ)/34650000000),((-5664730267:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((2091506341:ℚ)/5000000000),((2472283605227794575011806223117928230699900687285767865708131:ℚ)/23842921258812304687500000000000000000000000000000000000000000),((16985573433686318835435554149:ℚ)/44359680000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((3502176057:ℚ)/5000000000),((7140067843:ℚ)/10000000000),((-66380746273:ℚ)/104900000000),((-2862176057:ℚ)/5292500000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((996371161:ℚ)/2500000000),((45969584956370831558917236690075713073210982068225186395219289:ℚ)/442920047525356250000000000000000000000000000000000000000000000),((4241178001845496875124700509:ℚ)/11089920000000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7063969503:ℚ)/10000000000),((3584934979:ℚ)/5000000000),((-33354284769:ℚ)/52925000000),((-5783969503:ℚ)/10632500000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((1889118481:ℚ)/5000000000),((1719010503201101790853382347974794650734732024101802861202277769:ℚ)/16759203823980909863281250000000000000000000000000000000000000000),((16943719788700581883683082669:ℚ)/44359680000000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((7093776563:ℚ)/10000000000),((7199671047:ℚ)/10000000000),((-67036381517:ℚ)/106325000000),((-1937925521:ℚ)/3560000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((3670455411:ℚ)/10000000000),((1526700661455741094299936840335124652646111357398530976817197:ℚ)/14876686580471606445312500000000000000000000000000000000000000),((5644391542765846949589026343:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7123582553:ℚ)/10000000000),((57835769:ℚ)/80000000),((-538913459:ℚ)/854400000),((-5843582553:ℚ)/10727500000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((889891939:ℚ)/2500000000),((5483354163828398094366437256501981784893118647977138911:ℚ)/53404948026057600000000000000000000000000000000000000000),((5640865588344541300746201823:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-11:ℚ)/16),((-5:ℚ)/8),((223543359:ℚ)/312500000),((1814817551:ℚ)/2500000000),((-16922993061:ℚ)/26818750000),((-183543359:ℚ)/336718750),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3445273513:ℚ)/10000000000),((8986421735211612996661721915225871566469244819766563912149:ℚ)/87480284745807236433029174804687500000000000000000000000000),((16515611520628113833795821:ℚ)/43320000000000000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7183191381:ℚ)/10000000000),((7289068299:ℚ)/10000000000),((-68019751289:ℚ)/107750000000),((-159545713:ℚ)/292500000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((1663610523:ℚ)/5000000000),((687490649341356733442620313431470118690836263914401689823041:ℚ)/6689344993890380859375000000000000000000000000000000000000000),((16901342923429207078810527301:ℚ)/44359680000000000000000000000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((7212994247:ℚ)/10000000000),((3659432711:ℚ)/5000000000),((-34173759821:ℚ)/54112500000),((-5932994247:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((400624309:ℚ)/1250000000),((361303644057017244960504627252531792244968958136644880717897:ℚ)/3513886006294885253906250000000000000000000000000000000000000),((5630222314013090153072104223:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((3621398049:ℚ)/5000000000),((3689228401:ℚ)/5000000000),((-34501512411:ℚ)/54350000000),((-2981398049:ℚ)/5482500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3078095957:ℚ)/10000000000),((13958086804045943693575261615772061304152506517000179725016219:ℚ)/134045866122770117187500000000000000000000000000000000000000000),((4219989563013479776265524141:ℚ)/11089920000000000000000000000)⟩
theorem valid11 : Valid source21 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((1825599203:ℚ)/2500000000),((3719022223:ℚ)/5000000000),((-11609748151:ℚ)/18275000000),((-1505599203:ℚ)/2765000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1403862159:ℚ)/5000000000),((2713361152763227016443968422752526022804546124470751496617:ℚ)/26039007269465637207031250000000000000000000000000000000000),((351217557066110235590639623:ℚ)/924160000000000000000000000)⟩
theorem valid12 : Valid source21 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source21 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-11:ℚ)/16),((-5:ℚ)/8),((7361993627:ℚ)/10000000000),((3778604451:ℚ)/5000000000),((-35484648961:ℚ)/55300000000),((-2027331209:ℚ)/3750000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((39206897:ℚ)/156250000),((3965652022975335488374905467785333199305057188020829361:ℚ)/37158481274414062500000000000000000000000000000000000000),((5612265457849859000292319863:ℚ)/14786560000000000000000000000)⟩
theorem valid13 : Valid source21 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source21 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((1870293989:ℚ)/2500000000),((3838179761:ℚ)/5000000000),((-36139977371:ℚ)/56250000000),((-1550293989:ℚ)/2860000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((221328759:ℚ)/1250000000),((809754001379307375276545560215180108137093329621819537870057:ℚ)/7582255554199218750000000000000000000000000000000000000000000),((349856480039015348060800887:ℚ)/924160000000000000000000000)⟩
theorem valid14 : Valid source21 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source21 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((7600343849:ℚ)/10000000000),((269660619:ℚ)/312500000),((-2586266809:ℚ)/3575000000),((-2106781283:ℚ)/4320000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((738759457793869949381662818570598844025261605163299671:ℚ)/5337907910156250000000000000000000000000000000000000000),((386635053:ℚ)/1024000000)⟩
theorem valid15 : Valid source21 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((1069155491:ℚ)/1250000000),((526655537:ℚ)/500000000),((-5185210907:ℚ)/6480000000),((-909155491:ℚ)/2000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((280619931795110642644846984848441960739753450695524347:ℚ)/1700611200000000000000000000000000000000000000000000000),((386635053:ℚ)/1024000000)⟩
theorem valid16 : Valid source21 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((5228692867:ℚ)/5000000000),((14337766319:ℚ)/10000000000),((-145555429509:ℚ)/160000000000),((-1529564289:ℚ)/3680000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((116333623154576432449687145798723611388327:ℚ)/541696000000000000000000000000000000000000),((386635053:ℚ)/1024000000)⟩
theorem valid17 : Valid source21 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source21 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source21 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4253:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source21 nn0 nn1 Qcell ((4253:ℚ)/6400) ((431:ℚ)/640) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source21 nn0 nn1 Qcell ((1049:ℚ)/1600) ((431:ℚ)/640) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source21 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source21 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source21 nn0 nn1 Qcell ((431:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC06
#check @N11Formalization.C450Source21GroupedC06.bound
#print axioms N11Formalization.C450Source21GroupedC06.valid0
#print axioms N11Formalization.C450Source21GroupedC06.valid1
#print axioms N11Formalization.C450Source21GroupedC06.valid2
#print axioms N11Formalization.C450Source21GroupedC06.valid3
#print axioms N11Formalization.C450Source21GroupedC06.valid4
#print axioms N11Formalization.C450Source21GroupedC06.valid5
#print axioms N11Formalization.C450Source21GroupedC06.valid6
#print axioms N11Formalization.C450Source21GroupedC06.valid7
#print axioms N11Formalization.C450Source21GroupedC06.valid8
#print axioms N11Formalization.C450Source21GroupedC06.valid9
#print axioms N11Formalization.C450Source21GroupedC06.valid10
#print axioms N11Formalization.C450Source21GroupedC06.valid11
#print axioms N11Formalization.C450Source21GroupedC06.valid12
#print axioms N11Formalization.C450Source21GroupedC06.valid13
#print axioms N11Formalization.C450Source21GroupedC06.valid14
#print axioms N11Formalization.C450Source21GroupedC06.valid15
#print axioms N11Formalization.C450Source21GroupedC06.valid16
#print axioms N11Formalization.C450Source21GroupedC06.valid17
#print axioms N11Formalization.C450Source21GroupedC06.bound
#print axioms N11Formalization.C450Source21GroupedC06.endpoint_checks
