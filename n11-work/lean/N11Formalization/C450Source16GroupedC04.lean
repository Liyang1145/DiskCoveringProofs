import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((6608925591:ℚ)/10000000000),((864436319:ℚ)/1250000000),((-10117672147:ℚ)/12400000000),((-17426776773:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5164138701:ℚ)/10000000000),((314693433852426487746785522221550133401321727919080656407:ℚ)/4740790785000000000000000000000000000000000000000000000000),((947317221527445649176040763:ℚ)/2334720000000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((1711708713:ℚ)/2500000000),((1394990517:ℚ)/2000000000),((-16342876721:ℚ)/20600000000),((-1511708713:ℚ)/2165625000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((140299753:ℚ)/312500000),((4906914625346646130801461955911726827325709111708952372263:ℚ)/81997038909843750000000000000000000000000000000000000000000),((59248040425736654170864187:ℚ)/145920000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((6906307481:ℚ)/10000000000),((7034413039:ℚ)/10000000000),((-82487369507:ℚ)/103950000000),((-18318922443:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((172231179:ℚ)/400000000),((1444979477383985238573269414963250568200697942225456643453509:ℚ)/24140957774547458496093750000000000000000000000000000000000000),((316259653796645725923808201:ℚ)/778240000000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((217680573:ℚ)/312500000),((1773467989:ℚ)/2500000000),((-20815083857:ℚ)/26225000000),((-578041719:ℚ)/826953125),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((2057151163:ℚ)/5000000000),((5179062167281874979264566737102804661755245208934771739383:ℚ)/86507821782296142578125000000000000000000000000000000000000),((48806989288038591819593:ℚ)/120000000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((1756311867:ℚ)/2500000000),((7123600851:ℚ)/10000000000),((-83646811063:ℚ)/105850000000),((-4668935601:ℚ)/6645312500),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((3914032061:ℚ)/10000000000),((98643894305902618395751401653281818465987278798956324468360161:ℚ)/1675920382398090986328125000000000000000000000000000000000000000),((59372857044076773332134547:ℚ)/145920000000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((7054981401:ℚ)/10000000000),((7153329377:ℚ)/10000000000),((-84033281901:ℚ)/106325000000),((-6254981401:ℚ)/8900000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((3810167389:ℚ)/10000000000),((10947548954723099462332912194646251597211730866020616525267:ℚ)/185958582255895080566406250000000000000000000000000000000000),((950370198965370556435397723:ℚ)/2334720000000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((177117873:ℚ)/250000000),((7183057539:ℚ)/10000000000),((-84419748007:ℚ)/106800000000),((-471353619:ℚ)/670468750),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((231471153:ℚ)/625000000),((1612214276632881043215939341782615556328950023386116896044361:ℚ)/27380466517265859375000000000000000000000000000000000000000000),((594234101514435413110667:ℚ)/1459200000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-13:ℚ)/16),((-3:ℚ)/4),((7114448031:ℚ)/10000000000),((7212785341:ℚ)/10000000000),((-84806209433:ℚ)/107275000000),((-18943344093:ℚ)/26937500000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3593898689:ℚ)/10000000000),((12364656274555520925074714037707698819756580724704223753917:ℚ)/209952683389937367439270019531250000000000000000000000000000),((951178803135818864271571403:ℚ)/2334720000000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((431:ℚ)/640),((8639:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((7144180739:ℚ)/10000000000),((722764911:ℚ)/1000000000),((-8499943843:ℚ)/10775000000),((-19032542217:ℚ)/26996875000),((4856560387:ℚ)/5000000000),((9719670101:ℚ)/10000000000),((9604357:ℚ)/40000000),((1740481551:ℚ)/5000000000),((106500060843388256864270943161374724999959031706270804233101:ℚ)/1823512830972934265136718750000000000000000000000000000000000),((317122243013098842924403361:ℚ)/778240000000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((431:ℚ)/640) ((8639:ℚ)/12800) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8639:ℚ)/12800),((4329:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7159046943:ℚ)/10000000000),((724251279:ℚ)/1000000000),((-8519266627:ℚ)/10798750000),((-6359046943:ℚ)/9018750000),((2426658193:ℚ)/2500000000),((9713120779:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((3423157643:ℚ)/10000000000),((747846962012380393856393221839584449099102820381446234381:ℚ)/12803336826099554357528686523437500000000000000000000000000),((951568743361511298847732427:ℚ)/2334720000000000000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((8639:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4329:ℚ)/6400),((8677:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((7173913049:ℚ)/10000000000),((3628688191:ℚ)/5000000000),((-14230982161:ℚ)/18037500000),((-19121739147:ℚ)/27115625000),((9700205687:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((306851119:ℚ)/1250000000),((3364399261:ℚ)/10000000000),((155114466429795235622885123735303230099577304918391008599459:ℚ)/2655308008111760101318359375000000000000000000000000000000000),((16697732053083330103701939:ℚ)/40960000000000000000000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((4329:ℚ)/6400) ((8677:ℚ)/12800) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8677:ℚ)/12800),((1087:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((449298691:ℚ)/625000000),((454514993:ℚ)/625000000),((-5348694909:ℚ)/6778906250),((-1197896073:ℚ)/1698437500),((9693839119:ℚ)/10000000000),((2425051423:ℚ)/2500000000),((2480870833:ℚ)/10000000000),((660927413:ℚ)/2000000000),((840006313747592084214254070333231430421130840767314638301:ℚ)/14377984340503552500158548355102539062500000000000000000000),((1239547760498233810009121:ℚ)/3040000000000000000000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1087:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((3601822483:ℚ)/5000000000),((7301966641:ℚ)/10000000000),((-85965566333:ℚ)/108700000000),((-9605467449:ℚ)/13646875000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((1621907749:ℚ)/5000000000),((7047042512086908755509771963708359975533568226347213801843771:ℚ)/119598315771687338867187500000000000000000000000000000000000000),((79365899132490977729928449:ℚ)/194560000000000000000000000)⟩
theorem valid12 : Valid source16 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source16 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((452086031:ℚ)/625000000),((7331693053:ℚ)/10000000000),((-7850182699:ℚ)/9925000000),((-402086031:ℚ)/571093750),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((3118744983:ℚ)/10000000000),((601321972927686495536092887782983254410176197132461414293:ℚ)/10203668466507873535156250000000000000000000000000000000000),((1240617890688784634094801:ℚ)/3040000000000000000000000)⟩
theorem valid13 : Valid source16 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source16 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-13:ℚ)/16),((-3:ℚ)/4),((1815776911:ℚ)/2500000000),((7361419129:ℚ)/10000000000),((-86738448677:ℚ)/109650000000),((-4847330733:ℚ)/6882812500),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((23908991:ℚ)/80000000),((69290888970091116312201008740528136190455031111470743041667:ℚ)/1175598010714064941406250000000000000000000000000000000000000),((19858295168975743802671161:ℚ)/48640000000000000000000000)⟩
theorem valid14 : Valid source16 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source16 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source16 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((1458567683:ℚ)/2000000000),((7391144873:ℚ)/10000000000),((-87124883349:ℚ)/110125000000),((-556529007:ℚ)/790000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((713190131:ℚ)/2500000000),((599795960460973768005153050212453190814820338161570068267:ℚ)/10174709142878055572509765625000000000000000000000000000000),((12714688984444000067839649:ℚ)/31129600000000000000000000)⟩
theorem valid15 : Valid source16 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source16 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((7322568813:ℚ)/10000000000),((3725297691:ℚ)/5000000000),((-43948869983:ℚ)/55300000000),((-19567706439:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((542058173:ℚ)/2000000000),((35181447962271393734309067077141394318686530356127508221543:ℚ)/587146588934916992187500000000000000000000000000000000000000),((954437408633922238493033987:ℚ)/2334720000000000000000000000)⟩
theorem valid16 : Valid source16 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-13:ℚ)/16),((-3:ℚ)/4),((738202851:ℚ)/1000000000),((7510044613:ℚ)/10000000000),((-88670579969:ℚ)/111550000000),((-658202851:ℚ)/937500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2400775389:ℚ)/10000000000),((228457700273373534493850089334682059389981097751920047:ℚ)/3812424908409118652343750000000000000000000000000000000),((9552437996995121613141923:ℚ)/23347200000000000000000000)⟩
theorem valid17 : Valid source16 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source16 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source16 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((297659471:ℚ)/400000000),((7628939371:ℚ)/10000000000),((-90216211823:ℚ)/112500000000),((-72452583:ℚ)/104000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1022983669:ℚ)/5000000000),((1161761805370941685844964784370969410370243487138372889121:ℚ)/18798980712890625000000000000000000000000000000000000000000),((510129830739202119533881:ℚ)/1245184000000000000000000)⟩
theorem valid18 : Valid source16 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-13:ℚ)/16),((-3:ℚ)/4),((3780199573:ℚ)/5000000000),((8104473237:ℚ)/10000000000),((-8763468371:ℚ)/10400000000),((-10140598719:ℚ)/15250000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((1021290373:ℚ)/10000000000),((5474115494872689445172230384222143887073563502518174627:ℚ)/75461880000000000000000000000000000000000000000000000000),((79697873906720551171483089:ℚ)/194560000000000000000000000)⟩
theorem valid19 : Valid source16 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((4017998981:ℚ)/5000000000),((1715988879:ℚ)/2000000000),((-20515855427:ℚ)/24400000000),((-3617998981:ℚ)/5400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((59234916219288982908762669670727991979074240250435720109:ℚ)/827345745000000000000000000000000000000000000000000000000),((419444937:ℚ)/1024000000)⟩
theorem valid20 : Valid source16 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((851152643:ℚ)/1000000000),((10481380943:ℚ)/10000000000),((-42432650753:ℚ)/43200000000),((-2313457929:ℚ)/4000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((127715171712113431906722524874679476064180127954606597:ℚ)/1180980000000000000000000000000000000000000000000000000),((419444937:ℚ)/1024000000)⟩
theorem valid21 : Valid source16 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((10413137643:ℚ)/10000000000),((7141533273:ℚ)/5000000000),(-1:ℚ),((-9613137643:ℚ)/18400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2583450404239466461247813:ℚ)/21160000000000000000000000),((419444937:ℚ)/1024000000)⟩
theorem valid22 : Valid source16 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet22 valid22
private theorem node0_2 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source16 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4253:ℚ)/6400) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source16 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((4253:ℚ)/6400) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source16 nn0 nn1 Qcell ((4253:ℚ)/6400) ((431:ℚ)/640) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source16 nn0 nn1 Qcell ((8639:ℚ)/12800) ((8677:ℚ)/12800) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source16 nn0 nn1 Qcell ((431:ℚ)/640) ((8677:ℚ)/12800) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source16 nn0 nn1 Qcell ((4253:ℚ)/6400) ((8677:ℚ)/12800) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((8677:ℚ)/12800) :=
  cell_join node0_5 node5_11
private theorem node12_14 :
    CellBound source16 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source16 nn0 nn1 Qcell ((8677:ℚ)/12800) ((2193:ℚ)/3200) :=
  cell_join leaf11 node12_14
private theorem node15_17 :
    CellBound source16 nn0 nn1 Qcell ((881:ℚ)/1280) ((2231:ℚ)/3200) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source16 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf14 node15_17
private theorem node11_17 :
    CellBound source16 nn0 nn1 Qcell ((8677:ℚ)/12800) ((2231:ℚ)/3200) :=
  cell_join node11_14 node14_17
private theorem node18_20 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source16 nn0 nn1 Qcell ((2231:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf17 node18_20
private theorem node21_23 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf20 node21_23
private theorem node17_23 :
    CellBound source16 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node17_20 node20_23
private theorem node11_23 :
    CellBound source16 nn0 nn1 Qcell ((8677:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node11_17 node17_23
private theorem node0_23 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_23
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_23
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22]
theorem packet_count : packets.length = 23 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC04
#check @N11Formalization.C450Source16GroupedC04.bound
#print axioms N11Formalization.C450Source16GroupedC04.valid0
#print axioms N11Formalization.C450Source16GroupedC04.valid1
#print axioms N11Formalization.C450Source16GroupedC04.valid2
#print axioms N11Formalization.C450Source16GroupedC04.valid3
#print axioms N11Formalization.C450Source16GroupedC04.valid4
#print axioms N11Formalization.C450Source16GroupedC04.valid5
#print axioms N11Formalization.C450Source16GroupedC04.valid6
#print axioms N11Formalization.C450Source16GroupedC04.valid7
#print axioms N11Formalization.C450Source16GroupedC04.valid8
#print axioms N11Formalization.C450Source16GroupedC04.valid9
#print axioms N11Formalization.C450Source16GroupedC04.valid10
#print axioms N11Formalization.C450Source16GroupedC04.valid11
#print axioms N11Formalization.C450Source16GroupedC04.valid12
#print axioms N11Formalization.C450Source16GroupedC04.valid13
#print axioms N11Formalization.C450Source16GroupedC04.valid14
#print axioms N11Formalization.C450Source16GroupedC04.valid15
#print axioms N11Formalization.C450Source16GroupedC04.valid16
#print axioms N11Formalization.C450Source16GroupedC04.valid17
#print axioms N11Formalization.C450Source16GroupedC04.valid18
#print axioms N11Formalization.C450Source16GroupedC04.valid19
#print axioms N11Formalization.C450Source16GroupedC04.valid20
#print axioms N11Formalization.C450Source16GroupedC04.valid21
#print axioms N11Formalization.C450Source16GroupedC04.valid22
#print axioms N11Formalization.C450Source16GroupedC04.bound
#print axioms N11Formalization.C450Source16GroupedC04.endpoint_checks
