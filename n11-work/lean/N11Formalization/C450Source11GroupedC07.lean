import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((6395351219:ℚ)/10000000000),((834990341:ℚ)/1250000000),((-762990341:ℚ)/1240000000),((-51158160971:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1141509007:ℚ)/2000000000),((13689230336093787060065678706698972853126596135978332007:ℚ)/379263262800000000000000000000000000000000000000000000000),((19606856733801369061854793:ℚ)/115520000000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((414569703:ℚ)/625000000),((424925633:ℚ)/625000000),((-388925633:ℚ)/643750000),((-3331127327:ℚ)/6556250000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1274826823:ℚ)/2500000000),((15943751956781705736007966446004522279027065749762359753:ℚ)/458693650637435913085937500000000000000000000000000000000),((257408963969708609507243:ℚ)/1520000000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((3375995039:ℚ)/5000000000),((864711579:ℚ)/1250000000),((-792711579:ℚ)/1311250000),((-27183955351:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4769052871:ℚ)/10000000000),((8729859460797260872083086758245790006387545548327861621:ℚ)/251130263508792114257812500000000000000000000000000000000),((19546119246260891467937673:ℚ)/115520000000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/8),((-9:ℚ)/16),((6870860459:ℚ)/10000000000),((218035379:ℚ)/312500000),((-200035379:ℚ)/333750000),((-55437744131:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2208098453:ℚ)/5000000000),((34543945006299298791522654972887188764212557825116499:ℚ)/1011601968682193756103515625000000000000000000000000000),((1220273788186851183793873:ℚ)/7220000000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((866286757:ℚ)/1250000000),((54973207:ℚ)/78125000),((-100946414:ℚ)/168359375),((-6996580813:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2114765579:ℚ)/5000000000),((601841207656967968634960525814053631277773209492275993:ℚ)/17620613465621881186962127685546875000000000000000000000),((76234394912268083284597:ℚ)/451250000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((3494863313:ℚ)/5000000000),((1774001941:ℚ)/2500000000),((-1630001941:ℚ)/2717500000),((-28253769817:ℚ)/54825000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((1008696001:ℚ)/2500000000),((572421621580912737513571900007183440009380441363597358461:ℚ)/16755733265346264648437500000000000000000000000000000000000),((78030686679275923269708393:ℚ)/462080000000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-5:ℚ)/8),((-9:ℚ)/16),((3524579099:ℚ)/5000000000),((3562862997:ℚ)/5000000000),((-1091620999:ℚ)/1827500000),((-28521211891:ℚ)/55062500000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((1915359629:ℚ)/5000000000),((250704795683978307186306980110376806660089967101225864671:ℚ)/7401913400792260742187500000000000000000000000000000000000),((311949771433088887347785577:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((7078873617:ℚ)/10000000000),((178886099:ℚ)/250000000),((-164486099:ℚ)/275312500),((-57309862553:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((931178939:ℚ)/2500000000),((32426583121496933398220166580406411806300885562745110719:ℚ)/957236636161967468261718750000000000000000000000000000000),((779708814183097072803353:ℚ)/4620800000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((7108588797:ℚ)/10000000000),((1437032333:ℚ)/2000000000),((-1321832333:ℚ)/2212000000),((-57577299173:ℚ)/111075000000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((451969457:ℚ)/1250000000),((11310225345654269090249659868242755354972928908333273462733:ℚ)/333832043096187300000000000000000000000000000000000000000000),((49890791710935340604944217:ℚ)/295731200000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7138303739:ℚ)/10000000000),((901859889:ℚ)/1250000000),((-276619963:ℚ)/462812500),((-57844733651:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3503562617:ℚ)/10000000000),((52247698284147846537003026113516158884895380373395709349:ℚ)/1541929093358554935455322265625000000000000000000000000000),((19484471186844715838640913:ℚ)/115520000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((7168018447:ℚ)/10000000000),((1448919261:ℚ)/2000000000),((-1333719261:ℚ)/2231000000),((-58112166023:ℚ)/112025000000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((338781493:ℚ)/1000000000),((1889074495562801415943954634988292184797024100041331835869:ℚ)/55742777860160537750000000000000000000000000000000000000000),((49869727687766249793032313:ℚ)/295731200000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-5:ℚ)/8),((-9:ℚ)/16),((1799433231:ℚ)/2500000000),((7274313247:ℚ)/10000000000),((-6698313247:ℚ)/11202500000),((-14594899079:ℚ)/28125000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((3268134391:ℚ)/10000000000),((94229383711117330655648056703850249245231912361123103:ℚ)/2780160884064102172851562500000000000000000000000000000),((1246480901438010508798318577:ℚ)/7393280000000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((7227447173:ℚ)/10000000000),((7304029941:ℚ)/10000000000),((-2242676647:ℚ)/3750000000),((-58647024557:ℚ)/112975000000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((3144071351:ℚ)/10000000000),((76051515807199950953011218633095343742760644284985151682469:ℚ)/2243557727050781250000000000000000000000000000000000000000000),((1246219283646239435572996393:ℚ)/7393280000000000000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((1814290299:ℚ)/2500000000),((7333746391:ℚ)/10000000000),((-6757746391:ℚ)/11297500000),((-14728612691:ℚ)/28362500000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((3015084297:ℚ)/10000000000),((3932413589099169054869370911009060658420699650502850572479:ℚ)/115994144936326073974609375000000000000000000000000000000000),((1245958338795645933895110593:ℚ)/7393280000000000000000000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((3643437499:ℚ)/5000000000),((7393178567:ℚ)/10000000000),((-6817178567:ℚ)/11345000000),((-29590937491:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2880511207:ℚ)/10000000000),((6380892103625578303650051617163299450592482452277806614887:ℚ)/186623183240578906250000000000000000000000000000000000000000),((1245864679192438092761666017:ℚ)/7393280000000000000000000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((918287743:ℚ)/1250000000),((37263049:ℚ)/50000000),((-34383049:ℚ)/57200000),((-7464589687:ℚ)/14418750000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2591089083:ℚ)/10000000000),((2771871143429655802908717482821102361348946502163:ℚ)/81059155112203125000000000000000000000000000000000),((31133687328344211409153:ℚ)/184832000000000000000000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((3702864017:ℚ)/5000000000),((7512040113:ℚ)/10000000000),((-2312013371:ℚ)/3845000000),((-30125776153:ℚ)/58150000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2265910539:ℚ)/10000000000),((16434225385824299522778975893976536560417144576816813714811:ℚ)/480538821780094531250000000000000000000000000000000000000000),((1244832998144082720762739857:ℚ)/7393280000000000000000000000)⟩
theorem valid16 : Valid source11 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((933144161:ℚ)/1250000000),((1907724517:ℚ)/2500000000),((-1763724517:ℚ)/2907500000),((-7598297449:ℚ)/14775000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1886568689:ℚ)/10000000000),((51795093997724889691369313125105229569925588709474459277:ℚ)/1490430222737377929687500000000000000000000000000000000000),((2558564260455219:ℚ)/15200000000000000)⟩
theorem valid17 : Valid source11 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/8),((-9:ℚ)/16),((7584001369:ℚ)/10000000000),((7868603877:ℚ)/10000000000),((-2430867959:ℚ)/3940000000),((-61856012321:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((129794361:ℚ)/2000000000),((152798419281438014860198843121210853978146377592471779157:ℚ)/4267264939950000000000000000000000000000000000000000000000),((20440475325524151:ℚ)/121600000000000000)⟩
theorem valid18 : Valid source11 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((7821688357:ℚ)/10000000000),((4171989623:ℚ)/5000000000),((-3883989623:ℚ)/6100000000),((-63995195213:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((351317518782466586869229996657101016738415838691202252847:ℚ)/9307639631250000000000000000000000000000000000000000000000),((86049267:ℚ)/512000000)⟩
theorem valid19 : Valid source11 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((41485147:ℚ)/50000000),((5122561907:ℚ)/5000000000),((-4834561907:ℚ)/6480000000),((-341366323:ℚ)/800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((245384365557142016589653594040074731639444997123019569:ℚ)/5101833600000000000000000000000000000000000000000000000),((86049267:ℚ)/512000000)⟩
theorem valid20 : Valid source11 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((637379333:ℚ)/625000000),((7023233471:ℚ)/5000000000),((-6735233471:ℚ)/8000000000),((-5336413997:ℚ)/13800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((222700295256895721360007107740418854990727484613861469311:ℚ)/3808800000000000000000000000000000000000000000000000000000),((86049267:ℚ)/512000000)⟩
theorem valid21 : Valid source11 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet21 valid21
private theorem node0_2 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source11 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source11 nn0 nn1 Qcell ((4443:ℚ)/6400) ((4481:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((4481:ℚ)/6400) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4481:ℚ)/6400) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((4481:ℚ)/6400) :=
  cell_join node0_5 node5_11
private theorem node11_13 :
    CellBound source11 nn0 nn1 Qcell ((4481:ℚ)/6400) ((4519:ℚ)/6400) :=
  cell_join leaf11 leaf12
private theorem node14_16 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source11 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join leaf13 node14_16
private theorem node11_16 :
    CellBound source11 nn0 nn1 Qcell ((4481:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join node11_13 node13_16
private theorem node17_19 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf16 node17_19
private theorem node20_22 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf19 node20_22
private theorem node16_22 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node16_19 node19_22
private theorem node11_22 :
    CellBound source11 nn0 nn1 Qcell ((4481:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node11_16 node16_22
private theorem node0_22 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_22
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_22
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21]
theorem packet_count : packets.length = 22 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC07
#check @N11Formalization.C450Source11GroupedC07.bound
#print axioms N11Formalization.C450Source11GroupedC07.valid0
#print axioms N11Formalization.C450Source11GroupedC07.valid1
#print axioms N11Formalization.C450Source11GroupedC07.valid2
#print axioms N11Formalization.C450Source11GroupedC07.valid3
#print axioms N11Formalization.C450Source11GroupedC07.valid4
#print axioms N11Formalization.C450Source11GroupedC07.valid5
#print axioms N11Formalization.C450Source11GroupedC07.valid6
#print axioms N11Formalization.C450Source11GroupedC07.valid7
#print axioms N11Formalization.C450Source11GroupedC07.valid8
#print axioms N11Formalization.C450Source11GroupedC07.valid9
#print axioms N11Formalization.C450Source11GroupedC07.valid10
#print axioms N11Formalization.C450Source11GroupedC07.valid11
#print axioms N11Formalization.C450Source11GroupedC07.valid12
#print axioms N11Formalization.C450Source11GroupedC07.valid13
#print axioms N11Formalization.C450Source11GroupedC07.valid14
#print axioms N11Formalization.C450Source11GroupedC07.valid15
#print axioms N11Formalization.C450Source11GroupedC07.valid16
#print axioms N11Formalization.C450Source11GroupedC07.valid17
#print axioms N11Formalization.C450Source11GroupedC07.valid18
#print axioms N11Formalization.C450Source11GroupedC07.valid19
#print axioms N11Formalization.C450Source11GroupedC07.valid20
#print axioms N11Formalization.C450Source11GroupedC07.valid21
#print axioms N11Formalization.C450Source11GroupedC07.bound
#print axioms N11Formalization.C450Source11GroupedC07.endpoint_checks
