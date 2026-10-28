import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((1304122673:ℚ)/2000000000),((1363794953:ℚ)/2000000000),((-8906564671:ℚ)/9920000000),((-15545594749:ℚ)/20600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5394809217:ℚ)/10000000000),((4320611921760432627542296412232667175131:ℚ)/101136870080000000000000000000000000000000),((37996634331287467018432837:ℚ)/118292480000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((675827531:ℚ)/1000000000),((138755773:ℚ)/200000000),((-907290411:ℚ)/1030000000),((-8081757903:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((190040203:ℚ)/400000000),((72606113656388200513272686305444101223394832856442853:ℚ)/1834774602549743652343750000000000000000000000000000000),((380749126683803090629597:ℚ)/1182924800000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((6877101879:ℚ)/10000000000),((1749298683:ℚ)/2500000000),((-11445090781:ℚ)/13112500000),((-82362324427:ℚ)/105850000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4396943107:ℚ)/10000000000),((150392298001974102203013847996424724516478111031842375938067:ℚ)/3946919368817261505126953125000000000000000000000000000000000),((178659659053228870093498631:ℚ)/554496000000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((6936514131:ℚ)/10000000000),((352830013:ℚ)/500000000),((-2309810091:ℚ)/2646250000),((-83134683703:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((1052386797:ℚ)/2500000000),((26209758719131000591604066749659713539836628113180336131:ℚ)/688040348424435424804687500000000000000000000000000000000),((2384575898819830349329117:ℚ)/7393280000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((174898143:ℚ)/250000000),((3543151411:ℚ)/5000000000),((-7734019959:ℚ)/8900000000),((-2097675859:ℚ)/2681875000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((4013958123:ℚ)/10000000000),((27084323118085131457546726341293602707192581462938272082959:ℚ)/724350966065234375000000000000000000000000000000000000000000),((238579959196536551104256253:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-7:ℚ)/8),((-13:ℚ)/16),((878203909:ℚ)/1250000000),((28464021:ℚ)/40000000),((-186448147:ℚ)/214550000),((-10536650817:ℚ)/13468750000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((122272127:ℚ)/312500000),((26795238374160947993745782822756284064029012380129061:ℚ)/716638492637652880859375000000000000000000000000000000),((45830848833647660532839:ℚ)/141950976000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((881917083:ℚ)/1250000000),((7145707547:ℚ)/10000000000),((-46819952829:ℚ)/53875000000),((-10584922079:ℚ)/13528125000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((59514221:ℚ)/156250000),((14266626131111341581905718485829821546164890159953109762244889:ℚ)/381571387359830474853515625000000000000000000000000000000000000),((955298901321394000554537837:ℚ)/2957312000000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4329:ℚ)/6400),((8677:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7085041899:ℚ)/10000000000),((7160558647:ℚ)/10000000000),((-46923910529:ℚ)/54112500000),((-85065544687:ℚ)/108462500000),((9700205687:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((306851119:ℚ)/1250000000),((3702349591:ℚ)/10000000000),((57547848209237007874836538772983625212311782599715104761963589:ℚ)/1553355184745379659271240234375000000000000000000000000000000000),((955543690406318734257124037:ℚ)/2957312000000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((4329:ℚ)/6400) ((8677:ℚ)/12800) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((8677:ℚ)/12800),((1087:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((3549947229:ℚ)/5000000000),((1435081943:ℚ)/2000000000),((-9405573601:ℚ)/10846250000),((-42629313977:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((2425051423:ℚ)/2500000000),((2480870833:ℚ)/10000000000),((729591553:ℚ)/2000000000),((2727291297767450217290156578419285455940440628097278942641:ℚ)/73615279823378188800811767578125000000000000000000000000000),((38231539547192117743399557:ℚ)/118292480000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1087:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1087:ℚ)/1600),((1743:ℚ)/2560),((-7:ℚ)/8),((-13:ℚ)/16),((3557373489:ℚ)/5000000000),((7190260751:ℚ)/10000000000),((-47131825257:ℚ)/54350000000),((-42725855357:ℚ)/54468750000),((9687532673:ℚ)/10000000000),((2423459781:ℚ)/2500000000),((2506424897:ℚ)/10000000000),((449097513:ℚ)/1250000000),((3001129361184709548282828911828025985231041160611676168253:ℚ)/81005803987124633789062500000000000000000000000000000000000),((956033296141783822539900693:ℚ)/2957312000000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1743:ℚ)/2560) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1743:ℚ)/2560),((4367:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7129599461:ℚ)/10000000000),((1441022351:ℚ)/2000000000),((-9447156457:ℚ)/10893750000),((-85644792993:ℚ)/109175000000),((2420321489:ℚ)/2500000000),((4843766339:ℚ)/5000000000),((2531487941:ℚ)/10000000000),((3536779759:ℚ)/10000000000),((471965456563826950120109030163373773181774169204374781699:ℚ)/12739043963215517997741699218750000000000000000000000000000),((38251124511687942610358293:ℚ)/118292480000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((1743:ℚ)/2560) ((4367:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4367:ℚ)/6400),((8753:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((1428890381:ℚ)/2000000000),((902495341:ℚ)/1250000000),((-5917467387:ℚ)/6823437500),((-17167574953:ℚ)/21882500000),((483754929:ℚ)/500000000),((9681285961:ℚ)/10000000000),((639018949:ℚ)/2500000000),((1739958479:ℚ)/5000000000),((32023501420202853796486752828317557519336732478545245230451:ℚ)/864352435947011108696460723876953125000000000000000000000000),((14945670916366721914780733:ℚ)/46208000000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((4367:ℚ)/6400) ((8753:ℚ)/12800) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((8753:ℚ)/12800),((2193:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((7159304311:ℚ)/10000000000),((7234813669:ℚ)/10000000000),((-47443695683:ℚ)/54706250000),((-86030956043:ℚ)/109650000000),((4834485079:ℚ)/5000000000),((1935019717:ℚ)/2000000000),((2580203419:ℚ)/10000000000),((855537161:ℚ)/2500000000),((151938972824784847102857371173178399406760354827581758880327:ℚ)/4100972642104928936004638671875000000000000000000000000000000),((956767773691051400724369773:ℚ)/2957312000000000000000000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((8753:ℚ)/12800) ((2193:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2193:ℚ)/3200),((8791:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((179353917:ℚ)/250000000),((7249664579:ℚ)/10000000000),((-932306903:ℚ)/1075000000),((-2155600921:ℚ)/2747187500),((9662900309:ℚ)/10000000000),((9668970163:ℚ)/10000000000),((520776989:ℚ)/2000000000),((336342809:ℚ)/1000000000),((32313201298975869707846668225927792182312549472966340843:ℚ)/872154712945556640625000000000000000000000000000000000000),((957012617939366499310146013:ℚ)/2957312000000000000000000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((2193:ℚ)/3200) ((8791:ℚ)/12800) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((8791:ℚ)/12800),((881:ℚ)/1280),((-7:ℚ)/8),((-13:ℚ)/16),((1797252253:ℚ)/2500000000),((7264515459:ℚ)/10000000000),((-47651608213:ℚ)/54943750000),((-21604279289:ℚ)/27531250000),((4828444327:ℚ)/5000000000),((4831450157:ℚ)/5000000000),((2627133759:ℚ)/10000000000),((660740891:ℚ)/2000000000),((465797474121391959044109137402228676155902975764950664468739:ℚ)/12572068897656942152976989746093750000000000000000000000000000),((2871772414226527364513419799:ℚ)/8871936000000000000000000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell ((8791:ℚ)/12800) ((881:ℚ)/1280) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((881:ℚ)/1280),((8829:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7203861307:ℚ)/10000000000),((7279366307:ℚ)/10000000000),((-47755564149:ℚ)/55062500000),((-86610196991:ℚ)/110362500000),((301591713:ℚ)/312500000),((9656888659:ℚ)/10000000000),((2649962557:ℚ)/10000000000),((1621461127:ℚ)/5000000000),((20926780480040472232558872854803377231152018265737376688920323:ℚ)/564817749649372959136962890625000000000000000000000000000000000),((957502334066443480594358557:ℚ)/2957312000000000000000000000)⟩
theorem valid15 : Valid source12 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source12 nn0 nn1 Qcell ((881:ℚ)/1280) ((8829:ℚ)/12800) :=
  cell_of_packet source12 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((8829:ℚ)/12800),((553:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((1804678391:ℚ)/2500000000),((58353737:ℚ)/80000000),((-382876159:ℚ)/441450000),((-21700819083:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((9650934821:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((397627593:ℚ)/1250000000),((863403577389122610854587947384786313721762948286713:ℚ)/23303238030979541015625000000000000000000000000000000),((61295821180485439154117:ℚ)/189267968000000000000000)⟩
theorem valid16 : Valid source12 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source12 nn0 nn1 Qcell ((8829:ℚ)/12800) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((3616782893:ℚ)/5000000000),((7323918671:ℚ)/10000000000),((-48067430697:ℚ)/55300000000),((-43498177609:ℚ)/55537500000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3117933177:ℚ)/10000000000),((773765026551425297246284916544496825397498255182432636695137:ℚ)/20698911402293359375000000000000000000000000000000000000000000),((958236977365253922047333013:ℚ)/2957312000000000000000000000)⟩
theorem valid17 : Valid source12 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((7263270119:ℚ)/10000000000),((7353620097:ℚ)/10000000000),((-48275340679:ℚ)/55537500000),((-87382511547:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((2987897707:ℚ)/10000000000),((1383315672525017078960206011741067544194862214231527187941777:ℚ)/37006298240605318450927734375000000000000000000000000000000000),((2876180357006634675001857311:ℚ)/8871936000000000000000000000)⟩
theorem valid18 : Valid source12 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source12 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((729297431:ℚ)/1000000000),((1845830351:ℚ)/2500000000),((-12120812457:ℚ)/13943750000),((-8776866603:ℚ)/11202500000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((1426062539:ℚ)/5000000000),((34558112082514423880489251924392174885889246141135026418857:ℚ)/924529662093461704254150390625000000000000000000000000000000),((59951039429498743427046293:ℚ)/184832000000000000000000000)⟩
theorem valid19 : Valid source12 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-7:ℚ)/8),((-13:ℚ)/16),((3661339179:ℚ)/5000000000),((1482604519:ℚ)/2000000000),((-9738231633:ℚ)/11202500000),((-44077409327:ℚ)/56250000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((2709752427:ℚ)/10000000000),((1847393938457841844735386744886213955565535578313351:ℚ)/49425082383361816406250000000000000000000000000000000),((38388260520942993958771173:ℚ)/118292480000000000000000000)⟩
theorem valid20 : Valid source12 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source12 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((7352382267:ℚ)/10000000000),((7472424633:ℚ)/10000000000),((-49106972431:ℚ)/56250000000),((-88540969471:ℚ)/113450000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((2559678007:ℚ)/10000000000),((1512113975482532187259806538163768650614445783002683584552657:ℚ)/39769863224029541015625000000000000000000000000000000000000000),((7983543392546352868750871:ℚ)/24576000000000000000000000)⟩
theorem valid21 : Valid source12 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((926473709:ℚ)/1250000000),((7531826221:ℚ)/10000000000),((-49522783547:ℚ)/56725000000),((-11164158217:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2230130529:ℚ)/10000000000),((2216814835349107941398746917212045916103767303146329829981:ℚ)/58319744762680908203125000000000000000000000000000000000000),((961666411468771604121210813:ℚ)/2957312000000000000000000000)⟩
theorem valid22 : Valid source12 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((3735598269:ℚ)/5000000000),((3884714149:ℚ)/5000000000),((-25592999043:ℚ)/28600000000),((-45042777497:ℚ)/59100000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1843687229:ℚ)/10000000000),((11106035392743392328189754908102116863630609761392539697663:ℚ)/265981756553906250000000000000000000000000000000000000000000),((333376507:ℚ)/1024000000)⟩
theorem valid23 : Valid source12 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/8),((-13:ℚ)/16),((7708818877:ℚ)/10000000000),((2001756003:ℚ)/2500000000),((-13212292021:ℚ)/14775000000),((-93174645401:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((64950217967393262828544893997179798757397486895844345169:ℚ)/1562719094219970703125000000000000000000000000000000000000),((333376507:ℚ)/1024000000)⟩
theorem valid24 : Valid source12 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((794643359:ℚ)/1000000000),((132534353:ℚ)/156250000),((-877740471:ℚ)/953125000),((-1069595963:ℚ)/1440000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1760733655794434546641548739187079251575665659764781:ℚ)/38325119018554687500000000000000000000000000000000000),((333376507:ℚ)/1024000000)⟩
theorem valid25 : Valid source12 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((421082141:ℚ)/500000000),((2076546199:ℚ)/2000000000),(-1:ℚ),((-5122067833:ℚ)/8000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((247626460234552867792891743879667:ℚ)/4000000000000000000000000000000000),((333376507:ℚ)/1024000000)⟩
theorem valid26 : Valid source12 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((5161140439:ℚ)/5000000000),((14183355883:ℚ)/10000000000),(-1:ℚ),((-21191608569:ℚ)/36800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2307854906845408081540273:ℚ)/33856000000000000000000000),((333376507:ℚ)/1024000000)⟩
theorem valid27 : Valid source12 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet27 valid27
private theorem node1_3 :
    CellBound source12 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source12 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4291:ℚ)/6400) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source12 nn0 nn1 Qcell ((4291:ℚ)/6400) ((4329:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source12 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4329:ℚ)/6400) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((4329:ℚ)/6400) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source12 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1743:ℚ)/2560) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source12 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1743:ℚ)/2560) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source12 nn0 nn1 Qcell ((1743:ℚ)/2560) ((8753:ℚ)/12800) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source12 nn0 nn1 Qcell ((8753:ℚ)/12800) ((8791:ℚ)/12800) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source12 nn0 nn1 Qcell ((1743:ℚ)/2560) ((8791:ℚ)/12800) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source12 nn0 nn1 Qcell ((4329:ℚ)/6400) ((8791:ℚ)/12800) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((8791:ℚ)/12800) :=
  cell_join node0_7 node7_14
private theorem node15_17 :
    CellBound source12 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source12 nn0 nn1 Qcell ((8791:ℚ)/12800) ((553:ℚ)/800) :=
  cell_join leaf14 node15_17
private theorem node17_19 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_join leaf17 leaf18
private theorem node19_21 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf19 leaf20
private theorem node17_21 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join node17_19 node19_21
private theorem node14_21 :
    CellBound source12 nn0 nn1 Qcell ((8791:ℚ)/12800) ((45:ℚ)/64) :=
  cell_join node14_17 node17_21
private theorem node22_24 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf22 leaf23
private theorem node21_24 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf21 node22_24
private theorem node24_26 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf24 leaf25
private theorem node26_28 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf26 leaf27
private theorem node24_28 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node24_26 node26_28
private theorem node21_28 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node21_24 node24_28
private theorem node14_28 :
    CellBound source12 nn0 nn1 Qcell ((8791:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node14_21 node21_28
private theorem node0_28 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_14 node14_28
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_28
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27]
theorem packet_count : packets.length = 28 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC03
#check @N11Formalization.C450Source12GroupedC03.bound
#print axioms N11Formalization.C450Source12GroupedC03.valid0
#print axioms N11Formalization.C450Source12GroupedC03.valid1
#print axioms N11Formalization.C450Source12GroupedC03.valid2
#print axioms N11Formalization.C450Source12GroupedC03.valid3
#print axioms N11Formalization.C450Source12GroupedC03.valid4
#print axioms N11Formalization.C450Source12GroupedC03.valid5
#print axioms N11Formalization.C450Source12GroupedC03.valid6
#print axioms N11Formalization.C450Source12GroupedC03.valid7
#print axioms N11Formalization.C450Source12GroupedC03.valid8
#print axioms N11Formalization.C450Source12GroupedC03.valid9
#print axioms N11Formalization.C450Source12GroupedC03.valid10
#print axioms N11Formalization.C450Source12GroupedC03.valid11
#print axioms N11Formalization.C450Source12GroupedC03.valid12
#print axioms N11Formalization.C450Source12GroupedC03.valid13
#print axioms N11Formalization.C450Source12GroupedC03.valid14
#print axioms N11Formalization.C450Source12GroupedC03.valid15
#print axioms N11Formalization.C450Source12GroupedC03.valid16
#print axioms N11Formalization.C450Source12GroupedC03.valid17
#print axioms N11Formalization.C450Source12GroupedC03.valid18
#print axioms N11Formalization.C450Source12GroupedC03.valid19
#print axioms N11Formalization.C450Source12GroupedC03.valid20
#print axioms N11Formalization.C450Source12GroupedC03.valid21
#print axioms N11Formalization.C450Source12GroupedC03.valid22
#print axioms N11Formalization.C450Source12GroupedC03.valid23
#print axioms N11Formalization.C450Source12GroupedC03.valid24
#print axioms N11Formalization.C450Source12GroupedC03.valid25
#print axioms N11Formalization.C450Source12GroupedC03.valid26
#print axioms N11Formalization.C450Source12GroupedC03.valid27
#print axioms N11Formalization.C450Source12GroupedC03.bound
#print axioms N11Formalization.C450Source12GroupedC03.endpoint_checks
