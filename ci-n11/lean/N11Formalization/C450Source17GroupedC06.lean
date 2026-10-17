import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((409830197:ℚ)/625000000),((3430350693:ℚ)/5000000000),((-32933857623:ℚ)/49600000000),((-345830197:ℚ)/643750000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((265006583:ℚ)/500000000),((266865566954059293931317206129918785848200698461143116195399:ℚ)/4045474803200000000000000000000000000000000000000000000000000),((18457597133055955147808879:ℚ)/57760000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((6795438553:ℚ)/10000000000),((279190257:ℚ)/400000000),((-2687092827:ℚ)/4120000000),((-5771438553:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2321484267:ℚ)/5000000000),((3777884305461602481118910307818278817954350301693342788171:ℚ)/60121894176350000000000000000000000000000000000000000000000),((4715361019728854289328733879:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((3457249189:ℚ)/5000000000),((3519639911:ℚ)/5000000000),((-33916039021:ℚ)/52450000000),((-2945249189:ℚ)/5292500000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4279885669:ℚ)/10000000000),((58577533862249260933920408008590612315670160269155945051721:ℚ)/954569067942578125000000000000000000000000000000000000000000),((1177599058880275618678289551:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((6974024103:ℚ)/10000000000),((709880057:ℚ)/1000000000),((-6848680627:ℚ)/10585000000),((-5950024103:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((817417561:ℚ)/2000000000),((6173761593734720991340022165824972877989633137751131843:ℚ)/100535576025488281250000000000000000000000000000000000000),((14123686868258629036563616037:ℚ)/44359680000000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((54949587:ℚ)/78125000),((7128559973:ℚ)/10000000000),((-68814159703:ℚ)/106800000000),((-187798348:ℚ)/335234375),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((3885305517:ℚ)/10000000000),((66481183019250755910586932487578119059870009717609462844851471:ℚ)/1095218660690634375000000000000000000000000000000000000000000000),((861581334403907992356317:ℚ)/2707500000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-11:ℚ)/16),((-5:ℚ)/8),((3531653833:ℚ)/5000000000),((7158318739:ℚ)/10000000000),((-69141506129:ℚ)/107275000000),((-3019653833:ℚ)/5387500000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((472574613:ℚ)/1250000000),((509980268547771242319867332376958451366463652993775568825251:ℚ)/8398107335597494697570800781250000000000000000000000000000000),((1176030480929888357473830359:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((141861351:ℚ)/200000000),((7188076877:ℚ)/10000000000),((-69468845647:ℚ)/107750000000),((-9337027:ℚ)/16650000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((3673054191:ℚ)/10000000000),((1645932338275380696639245332533153881885821082391192240011279:ℚ)/27093826321408081054687500000000000000000000000000000000000000),((5643429538434627365232293:ℚ)/17743872000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((1780706699:ℚ)/2500000000),((1804458599:ℚ)/2500000000),((-17449044589:ℚ)/27056250000),((-1524706699:ℚ)/2717500000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1781210093:ℚ)/5000000000),((40040175652147007831927105691327488491717909396198761609923:ℚ)/658853626180290985107421875000000000000000000000000000000000),((293849433484023336625630831:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7152585413:ℚ)/10000000000),((7247591303:ℚ)/10000000000),((-70123504333:ℚ)/108700000000),((-6128585413:ℚ)/10917500000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((172419841:ℚ)/500000000),((26439947793198920737446350665203692301823333863163759281434439:ℚ)/434902966442499414062500000000000000000000000000000000000000000),((4700320884678664294176495439:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7182343409:ℚ)/10000000000),((7277347607:ℚ)/10000000000),((-70450823677:ℚ)/109175000000),((-6158343409:ℚ)/10965000000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((416329431:ℚ)/1250000000),((6915024456094853868745874643585883595892575343938083220679847:ℚ)/113702087963067736816406250000000000000000000000000000000000000),((4699047795350075748549251911:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-11:ℚ)/16),((-5:ℚ)/8),((7212100791:ℚ)/10000000000),((1461420663:ℚ)/2000000000),((-4718542431:ℚ)/7310000000),((-6188100791:ℚ)/11012500000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((3208723959:ℚ)/10000000000),((14410274591804705589857718033240189057084756918314499981047:ℚ)/236861228825352343750000000000000000000000000000000000000000),((14093315002949772588242444933:ℚ)/44359680000000000000000000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((7241857569:ℚ)/10000000000),((1834214609:ℚ)/2500000000),((-17776360699:ℚ)/27531250000),((-888265367:ℚ)/1580000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((123286773:ℚ)/400000000),((4644196163302381988834096325735640754719989936242265727771:ℚ)/76310318571585416793823242187500000000000000000000000000000),((14089477504012565587995592373:ℚ)/44359680000000000000000000000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((5817291:ℚ)/8000000),((7396366943:ℚ)/10000000000),((-71760036373:ℚ)/110600000000),((-4998091:ℚ)/8924000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((295037349:ℚ)/1000000000),((11572442834617769721724306018250392626369739679140924511127587:ℚ)/187886908459173437500000000000000000000000000000000000000000000),((9014803768891168073933:ℚ)/28390195200000000000000)⟩
theorem valid12 : Valid source17 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-11:ℚ)/16),((-5:ℚ)/8),((7331124351:ℚ)/10000000000),((7455873189:ℚ)/10000000000),((-72414605079:ℚ)/111550000000),((-6307124351:ℚ)/11250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1333959717:ℚ)/5000000000),((871921429679239494938799272507600316691911285928845911:ℚ)/14149205845642089843750000000000000000000000000000000000),((14077910308415474195968050293:ℚ)/44359680000000000000000000000)⟩
theorem valid13 : Valid source17 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source17 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source17 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((7390632653:ℚ)/10000000000),((7574879119:ℚ)/10000000000),((-73723670309:ℚ)/112500000000),((-6366632653:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1176345141:ℚ)/5000000000),((521414246208102299504389617195456425274981996038970055911703:ℚ)/8271551513671875000000000000000000000000000000000000000000000),((4690051086060226120854876479:ℚ)/14786560000000000000000000000)⟩
theorem valid14 : Valid source17 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((1501928519:ℚ)/2000000000),((7812866219:ℚ)/10000000000),((-76341528409:ℚ)/114400000000),((-432376173:ℚ)/788000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((771776063:ℚ)/5000000000),((2984113195548339847924066406847700915134760835705554825049193:ℚ)/45394219785200000000000000000000000000000000000000000000000000),((187393729793159593388102391:ℚ)/591462400000000000000000000)⟩
theorem valid15 : Valid source17 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-11:ℚ)/16),((-5:ℚ)/8),((7747637331:ℚ)/10000000000),((1006352861:ℚ)/1250000000),((-9869881471:ℚ)/14775000000),((-6723637331:ℚ)/12200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((7386991157523606167155546519493321722091019140583558875149:ℚ)/112515774783837890625000000000000000000000000000000000000000),((324159037:ℚ)/1024000000)⟩
theorem valid16 : Valid source17 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((1996400289:ℚ)/2500000000),((8526655677:ℚ)/10000000000),((-84193212447:ℚ)/122000000000),((-1740400289:ℚ)/3240000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2621341574884537873232864770775140153301661636252308011331639:ℚ)/37230558525000000000000000000000000000000000000000000000000000),((324159037:ℚ)/1024000000)⟩
theorem valid17 : Valid source17 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((528840437:ℚ)/625000000),((2607298541:ℚ)/2500000000),((-26280283951:ℚ)/32400000000),((-464840437:ℚ)/1000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((30732354173312382660443998254262355138602311884837239309:ℚ)/318864600000000000000000000000000000000000000000000000000),((324159037:ℚ)/1024000000)⟩
theorem valid18 : Valid source17 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((414561009:ℚ)/400000000),((2846434339:ℚ)/2000000000),((-29390777729:ℚ)/32000000000),((-373601009:ℚ)/883200000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2423060428052236279083426681307712479891:ℚ)/19501056000000000000000000000000000000000),((324159037:ℚ)/1024000000)⟩
theorem valid19 : Valid source17 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet19 valid19
private theorem node0_2 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source17 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4291:ℚ)/6400) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source17 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4291:ℚ)/6400) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((4291:ℚ)/6400) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source17 nn0 nn1 Qcell ((4291:ℚ)/6400) ((4329:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source17 nn0 nn1 Qcell ((4329:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source17 nn0 nn1 Qcell ((4291:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source17 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source17 nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source17 nn0 nn1 Qcell ((2193:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound source17 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC06
#check @N11Formalization.C450Source17GroupedC06.bound
#print axioms N11Formalization.C450Source17GroupedC06.valid0
#print axioms N11Formalization.C450Source17GroupedC06.valid1
#print axioms N11Formalization.C450Source17GroupedC06.valid2
#print axioms N11Formalization.C450Source17GroupedC06.valid3
#print axioms N11Formalization.C450Source17GroupedC06.valid4
#print axioms N11Formalization.C450Source17GroupedC06.valid5
#print axioms N11Formalization.C450Source17GroupedC06.valid6
#print axioms N11Formalization.C450Source17GroupedC06.valid7
#print axioms N11Formalization.C450Source17GroupedC06.valid8
#print axioms N11Formalization.C450Source17GroupedC06.valid9
#print axioms N11Formalization.C450Source17GroupedC06.valid10
#print axioms N11Formalization.C450Source17GroupedC06.valid11
#print axioms N11Formalization.C450Source17GroupedC06.valid12
#print axioms N11Formalization.C450Source17GroupedC06.valid13
#print axioms N11Formalization.C450Source17GroupedC06.valid14
#print axioms N11Formalization.C450Source17GroupedC06.valid15
#print axioms N11Formalization.C450Source17GroupedC06.valid16
#print axioms N11Formalization.C450Source17GroupedC06.valid17
#print axioms N11Formalization.C450Source17GroupedC06.valid18
#print axioms N11Formalization.C450Source17GroupedC06.valid19
#print axioms N11Formalization.C450Source17GroupedC06.bound
#print axioms N11Formalization.C450Source17GroupedC06.endpoint_checks
