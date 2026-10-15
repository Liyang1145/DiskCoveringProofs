import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((667291429:ℚ)/1000000000),((6868722219:ℚ)/10000000000),((-17726166657:ℚ)/24800000000),((-6124205719:ℚ)/10110000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4990971823:ℚ)/10000000000),((3824078134394516949506411029697118324071770227140922798623383:ℚ)/48720010737600000000000000000000000000000000000000000000000000),((1065624157564990197281427:ℚ)/2310400000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((3396040397:ℚ)/5000000000),((3493921403:ℚ)/5000000000),((-3013921403:ℚ)/4212500000),((-31276444367:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((4652825207:ℚ)/10000000000),((584234473340619985634674733749556678018935621122153327311:ℚ)/7434734556463623046875000000000000000000000000000000000000),((26645796923538105218437123:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((1382246371:ℚ)/2000000000),((1761849499:ℚ)/2500000000),((-4565548497:ℚ)/6437500000),((-1419190009:ℚ)/2310000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((1072557417:ℚ)/2500000000),((847202429301322915665509795985599448231415303184930295727:ℚ)/11121560181999206542968750000000000000000000000000000000000),((11805911037953546000107:ℚ)/25600000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((348540093:ℚ)/500000000),((1776737477:ℚ)/2500000000),((-139703407:ℚ)/196875000),((-3225941023:ℚ)/5245000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((819548573:ℚ)/2000000000),((500171286002439405951781827537355010827119659762956793:ℚ)/6560134144949913024902343750000000000000000000000000000),((266393456035896723716003:ℚ)/577600000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-3:ℚ)/4),((-11:ℚ)/16),((1757592079:ℚ)/2500000000),((3568362331:ℚ)/5000000000),((-9265086993:ℚ)/13112500000),((-16293512869:ℚ)/26343750000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((389633169:ℚ)/1000000000),((3759645473976811884463717923809103413749068174091962664967:ℚ)/50068164971386779785156250000000000000000000000000000000000),((6658687512228593059350827:ℚ)/14440000000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((1765037561:ℚ)/2500000000),((716649863:ℚ)/1000000000),((-620649863:ℚ)/878125000),((-16375413171:ℚ)/26462500000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((3791836223:ℚ)/10000000000),((712472746657831853769983953717647731113801008941726170297:ℚ)/9483327797055149078369140625000000000000000000000000000000),((6658948766264369278655387:ℚ)/14440000000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7089931319:ℚ)/10000000000),((3598135911:ℚ)/5000000000),((-9354407733:ℚ)/13231250000),((-65829244509:ℚ)/106325000000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((736905717:ℚ)/2000000000),((9841644124179484580097039860275963941134445999350443517481387:ℚ)/130931279874850858306884765625000000000000000000000000000000000),((106547263683309658395774267:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((1423942311:ℚ)/2000000000),((903255531:ℚ)/1250000000),((-2349766593:ℚ)/3322656250),((-13231365421:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((3574154937:ℚ)/10000000000),((78663691946277698412589703717889061603069302943327602326779:ℚ)/1046017025189409828186035156250000000000000000000000000000000),((4262050018856792951679387:ℚ)/9241600000000000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((3574745481:ℚ)/5000000000),((7255815919:ℚ)/10000000000),((-6295815919:ℚ)/8900000000),((-33242200291:ℚ)/53637500000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((1730210677:ℚ)/5000000000),((47686854673076187557830023461836822399588291340021694353361:ℚ)/633807095307080078125000000000000000000000000000000000000000),((1402041324143736770638393:ℚ)/3040000000000000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-3:ℚ)/4),((-11:ℚ)/16),((448704347:ℚ)/625000000),((1457117369:ℚ)/2000000000),((-6191439:ℚ)/8750000),((-4175747817:ℚ)/6734375000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3342984341:ℚ)/10000000000),((114348672248875739410569422276567108260617920361:ℚ)/1519108366966247558593750000000000000000000000000),((416245836646813310909473:ℚ)/902500000000000000000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((3604523667:ℚ)/5000000000),((1828839259:ℚ)/2500000000),((-4766517777:ℚ)/6734375000),((-33569760337:ℚ)/54112500000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((402679789:ℚ)/1250000000),((84185081107546646440375958308206282709707653254948537683383:ℚ)/1117884923905753344297409057617187500000000000000000000000000),((26640657780340484451513283:ℚ)/57760000000000000000000000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((7238824321:ℚ)/10000000000),((14690253:ℚ)/20000000),((-4256751:ℚ)/6012500),((-67467067531:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3095298621:ℚ)/10000000000),((6536741566600777921228041943282707398272393724367:ℚ)/86762617439379882812500000000000000000000000000000),((106566231459132553600484427:ℚ)/231040000000000000000000000)⟩
theorem valid11 : Valid source20 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source20 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((3634300261:ℚ)/5000000000),((7404663291:ℚ)/10000000000),((-19333989873:ℚ)/27175000000),((-11299100957:ℚ)/18275000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2963978209:ℚ)/10000000000),((641169059654014104669503698956085306361089530809549558603463:ℚ)/8377866632673132324218750000000000000000000000000000000000000),((26649190175207538356807187:ℚ)/57760000000000000000000000)⟩
theorem valid12 : Valid source20 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source20 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((458009413:ℚ)/625000000),((7464197291:ℚ)/10000000000),((-6504197291:ℚ)/9137500000),((-611157649:ℚ)/987500000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2682720983:ℚ)/10000000000),((53412172624943287883449945269717907819951900610267843183:ℚ)/697473409003543853759765625000000000000000000000000000000),((416419832783504079685493:ℚ)/902500000000000000000000)⟩
theorem valid13 : Valid source20 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source20 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/4),((-11:ℚ)/16),((7387697673:ℚ)/10000000000),((7583257203:ℚ)/10000000000),((-19869771609:ℚ)/27650000000),((-69104674403:ℚ)/112500000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2369200311:ℚ)/10000000000),((1648638004676464416424063921120445564246400138466150751:ℚ)/20901645716857910156250000000000000000000000000000000000),((106663851665081043718271163:ℚ)/231040000000000000000000000)⟩
theorem valid14 : Valid source20 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source20 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((7506783049:ℚ)/10000000000),((3851153391:ℚ)/5000000000),((-1123717797:ℚ)/1562500000),((-70414613539:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1567835703:ℚ)/10000000000),((19235409245246513028409627809915074758165568967555816833:ℚ)/243771076202392578125000000000000000000000000000000000000),((106582467844122924791756347:ℚ)/231040000000000000000000000)⟩
theorem valid15 : Valid source20 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((7625857239:ℚ)/10000000000),((2163596547:ℚ)/2500000000),((-5770789641:ℚ)/7150000000),((-71724429629:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((20779026581858199732816440674167415248495340454411099921:ℚ)/192164684765625000000000000000000000000000000000000000000),((7375747:ℚ)/16000000)⟩
theorem valid16 : Valid source20 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((8578107383:ℚ)/10000000000),((1055735701:ℚ)/1000000000),((-959735701:ℚ)/1080000000),((-82199181213:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((98435641864707823795473360694380801570415765771297:ℚ)/738112500000000000000000000000000000000000000000000),((7375747:ℚ)/16000000)⟩
theorem valid17 : Valid source20 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((10481321893:ℚ)/10000000000),((7180420583:ℚ)/5000000000),(-1:ℚ),((-103134540823:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1099722609877324571120927579:ℚ)/6094080000000000000000000000),((7375747:ℚ)/16000000)⟩
theorem valid18 : Valid source20 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source20 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source20 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source20 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4291:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source20 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4291:ℚ)/6400) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((4291:ℚ)/6400) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source20 nn0 nn1 Qcell ((4291:ℚ)/6400) ((4329:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source20 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source20 nn0 nn1 Qcell ((4329:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source20 nn0 nn1 Qcell ((4291:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source20 nn0 nn1 Qcell ((4291:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC05
#check @N11Formalization.C450Source20GroupedC05.bound
#print axioms N11Formalization.C450Source20GroupedC05.valid0
#print axioms N11Formalization.C450Source20GroupedC05.valid1
#print axioms N11Formalization.C450Source20GroupedC05.valid2
#print axioms N11Formalization.C450Source20GroupedC05.valid3
#print axioms N11Formalization.C450Source20GroupedC05.valid4
#print axioms N11Formalization.C450Source20GroupedC05.valid5
#print axioms N11Formalization.C450Source20GroupedC05.valid6
#print axioms N11Formalization.C450Source20GroupedC05.valid7
#print axioms N11Formalization.C450Source20GroupedC05.valid8
#print axioms N11Formalization.C450Source20GroupedC05.valid9
#print axioms N11Formalization.C450Source20GroupedC05.valid10
#print axioms N11Formalization.C450Source20GroupedC05.valid11
#print axioms N11Formalization.C450Source20GroupedC05.valid12
#print axioms N11Formalization.C450Source20GroupedC05.valid13
#print axioms N11Formalization.C450Source20GroupedC05.valid14
#print axioms N11Formalization.C450Source20GroupedC05.valid15
#print axioms N11Formalization.C450Source20GroupedC05.valid16
#print axioms N11Formalization.C450Source20GroupedC05.valid17
#print axioms N11Formalization.C450Source20GroupedC05.valid18
#print axioms N11Formalization.C450Source20GroupedC05.bound
#print axioms N11Formalization.C450Source20GroupedC05.endpoint_checks
