import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((3342034871:ℚ)/5000000000),((1375559901:ℚ)/2000000000),((-3768279703:ℚ)/3968000000),((-20994244097:ℚ)/25275000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4960218053:ℚ)/10000000000),((9028802576569916889272182307405990173342501:ℚ)/129920028633600000000000000000000000000000000),((3252131148661120516205559:ℚ)/6225920000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((1360586259:ℚ)/2000000000),((6996613189:ℚ)/10000000000),((-19197839567:ℚ)/20220000000),((-8564103813:ℚ)/10300000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((924180677:ℚ)/2000000000),((29653430380160104659541798605398790031474583318154867121:ℚ)/428240710452304687500000000000000000000000000000000000000),((81587978949638423909196839:ℚ)/155648000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((3460894363:ℚ)/5000000000),((7056019157:ℚ)/10000000000),((-19376057471:ℚ)/20600000000),((-21826260541:ℚ)/25987500000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((4256714511:ℚ)/10000000000),((12056522934805273087849377384638027680419606317272050079:ℚ)/183029104709472656250000000000000000000000000000000000000),((81730404883944276940185991:ℚ)/155648000000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((6981215967:ℚ)/10000000000),((708572193:ℚ)/1000000000),((-278073797:ℚ)/297000000),((-44068511769:ℚ)/52212500000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((162528449:ℚ)/400000000),((69524887832884833393745568208091505850276930413763667:ℚ)/1082117421394453125000000000000000000000000000000000000),((818016368228540370443391:ℚ)/1556480000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((7010929231:ℚ)/10000000000),((1778856141:ℚ)/2500000000),((-4888568423:ℚ)/5221250000),((-44276504617:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3963125533:ℚ)/10000000000),((785902087250916700794641681109693585910344603845604969041:ℚ)/12236704472516850738525390625000000000000000000000000000000),((5117055088334608138032279:ℚ)/9728000000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-15:ℚ)/16),((-7:ℚ)/8),((7040642261:ℚ)/10000000000),((3572563531:ℚ)/5000000000),((-9821690593:ℚ)/10490000000),((-44484495827:ℚ)/52687500000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((772117461:ℚ)/2000000000),((4114489139631890771920004858250495633742580240911239987551:ℚ)/64087251163375078125000000000000000000000000000000000000000),((1078212350821826469063421:ℚ)/2048000000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((843:ℚ)/1280),((8449:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((353517753:ℚ)/500000000),((357998913:ℚ)/500000000),((-984396739:ℚ)/1053750000),((-2234624271:ℚ)/2640312500),((4890720817:ℚ)/5000000000),((1957725423:ℚ)/2000000000),((83782417:ℚ)/400000000),((375539517:ℚ)/1000000000),((49658084952589598494742801424042669216986857195252193071:ℚ)/783059313877007574462890625000000000000000000000000000000),((10786812109727978271909:ℚ)/20480000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((843:ℚ)/1280) ((8449:ℚ)/12800) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((8449:ℚ)/12800),((2117:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((56681691:ℚ)/80000000),((286993177:ℚ)/400000000),((-789299531:ℚ)/844900000),((-358371837:ℚ)/423400000),((9774321709:ℚ)/10000000000),((9781441639:ℚ)/10000000000),((425706267:ℚ)/2000000000),((3701733253:ℚ)/10000000000),((46332251082070790881914749029810347324847795356999477:ℚ)/730718047756269453125000000000000000000000000000000000),((131224653715824971948111:ℚ)/249036800000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((8449:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2117:ℚ)/3200),((8487:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7100067633:ℚ)/10000000000),((1797420139:ℚ)/2500000000),((-4944260417:ℚ)/5292500000),((-650731499:ℚ)/768750000),((9767266893:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((2161672951:ℚ)/10000000000),((3647319011:ℚ)/10000000000),((925707641907651484799528488043471209578199127322196637:ℚ)/14601639006457214355468750000000000000000000000000000000),((5128190517213198973023239:ℚ)/9728000000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((2117:ℚ)/3200) ((8487:ℚ)/12800) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8487:ℚ)/12800),((4253:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((3557461917:ℚ)/5000000000),((1440906331:ℚ)/2000000000),((-3964318993:ℚ)/4243500000),((-22502233419:ℚ)/26581250000),((9760276751:ℚ)/10000000000),((4883633449:ℚ)/5000000000),((438804929:ℚ)/2000000000),((898029549:ℚ)/2500000000),((570405225409145726411438579240106092972260799321443794397:ℚ)/8998542440023339621582031250000000000000000000000000000000),((3283467645910892732407399:ℚ)/6225920000000000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((8487:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4253:ℚ)/6400),((341:ℚ)/512),((-15:ℚ)/16),((-7:ℚ)/8),((7129779981:ℚ)/10000000000),((7219382721:ℚ)/10000000000),((-19866148163:ℚ)/21265000000),((-45108459867:ℚ)/53281250000),((195067017:ℚ)/200000000),((2440069189:ℚ)/2500000000),((1112811311:ℚ)/5000000000),((3536093897:ℚ)/10000000000),((346039584271412171814930579025530689302774062561498169429:ℚ)/5459777781415916137695312500000000000000000000000000000000),((82122337187052684484505919:ℚ)/155648000000000000000000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((4253:ℚ)/6400) ((341:ℚ)/512) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((341:ℚ)/512),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((7144636071:ℚ)/10000000000),((3617116877:ℚ)/5000000000),((-9955350631:ℚ)/10656250000),((-15070817499:ℚ)/17800000000),((4873244381:ℚ)/5000000000),((1950670171:ℚ)/2000000000),((2256500263:ℚ)/10000000000),((869801571:ℚ)/2500000000),((172560446092661082434447640505100937699686597547277937:ℚ)/2723018248653411865234375000000000000000000000000000000),((20539496598307660717596311:ℚ)/38912000000000000000000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell ((341:ℚ)/512) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((267:ℚ)/400),((8563:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7159492107:ℚ)/10000000000),((1449816951:ℚ)/2000000000),((-3991050853:ℚ)/4272000000),((-45316444749:ℚ)/53518750000),((9739690061:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((1143344217:ℚ)/5000000000),((1710706109:ℚ)/5000000000),((84896129491216665122695996044940318861575577571335789434097:ℚ)/1339852235439309120000000000000000000000000000000000000000000),((3287745550747413404974959:ℚ)/6225920000000000000000000)⟩
theorem valid12 : Valid source16 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((8563:ℚ)/12800) :=
  cell_of_packet source16 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((8563:ℚ)/12800),((4291:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((896793511:ℚ)/1250000000),((7263935723:ℚ)/10000000000),((-19999807169:ℚ)/21407500000),((-5677554577:ℚ)/6704687500),((1216619291:ℚ)/1250000000),((4869845033:ℚ)/5000000000),((1158107867:ℚ)/5000000000),((1681332451:ℚ)/5000000000),((223520100280205856348028733292667392815353846552059620212167:ℚ)/3528132819709340059509277343750000000000000000000000000000000),((82229294310994778445352711:ℚ)/155648000000000000000000000)⟩
theorem valid13 : Valid source16 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source16 nn0 nn1 Qcell ((8563:ℚ)/12800) ((4291:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4291:ℚ)/6400),((8601:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((1437840803:ℚ)/2000000000),((363939333:ℚ)/500000000),((-1002217999:ℚ)/1072750000),((-9104885621:ℚ)/10751250000),((1215785143:ℚ)/1250000000),((9732954333:ℚ)/10000000000),((2345108749:ℚ)/10000000000),((1651456701:ℚ)/5000000000),((9616086281697503104831153525142887505479512000529869991:ℚ)/151804846625138052978515625000000000000000000000000000000),((205662382562349424298151:ℚ)/389120000000000000000000)⟩
theorem valid14 : Valid source16 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source16 nn0 nn1 Qcell ((4291:ℚ)/6400) ((8601:ℚ)/12800) :=
  cell_of_packet source16 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((8601:ℚ)/12800),((431:ℚ)/640),((-15:ℚ)/16),((-7:ℚ)/8),((450253743:ℚ)/625000000),((1458727513:ℚ)/2000000000),((-4017782539:ℚ)/4300500000),((-2851776201:ℚ)/3367187500),((607479381:ℚ)/625000000),((9726281149:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((324210213:ℚ)/1000000000),((24368810031460596183388553911441292575443116134025597671:ℚ)/384751367381183466796875000000000000000000000000000000000),((3292024596323941792478671:ℚ)/6225920000000000000000000)⟩
theorem valid15 : Valid source16 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source16 nn0 nn1 Qcell ((8601:ℚ)/12800) ((431:ℚ)/640) :=
  cell_of_packet source16 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((431:ℚ)/640),((8639:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((1804728927:ℚ)/2500000000),((7308488439:ℚ)/10000000000),((-20133465317:ℚ)/21550000000),((-11433102489:ℚ)/13498437500),((4856560387:ℚ)/5000000000),((9719670101:ℚ)/10000000000),((9604357:ℚ)/40000000),((3180170221:ℚ)/10000000000),((22670816372145723681887664835461328813220993392918836916697:ℚ)/357990249025361328125000000000000000000000000000000000000000),((82336279962851775596809839:ℚ)/155648000000000000000000000)⟩
theorem valid16 : Valid source16 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source16 nn0 nn1 Qcell ((431:ℚ)/640) ((8639:ℚ)/12800) :=
  cell_of_packet source16 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((8639:ℚ)/12800),((4329:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((289350859:ℚ)/400000000),((7323339281:ℚ)/10000000000),((-20178017843:ℚ)/21597500000),((-1833456013:ℚ)/2164500000),((2426658193:ℚ)/2500000000),((9713120779:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((311705081:ℚ)/1000000000),((933928854268333154866621557091137368933939325559272539211869:ℚ)/14749444023666686619873046875000000000000000000000000000000000),((82371948186777260876035999:ℚ)/155648000000000000000000000)⟩
theorem valid17 : Valid source16 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source16 nn0 nn1 Qcell ((8639:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((4329:ℚ)/6400),((8677:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((1812156797:ℚ)/2500000000),((7338190093:ℚ)/10000000000),((-20222570279:ℚ)/21645000000),((-11485097579:ℚ)/13557812500),((9700205687:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((306851119:ℚ)/1250000000),((305267017:ℚ)/1000000000),((871486349878129777039199866956827757068431537378735348478783:ℚ)/13765116714051364365234375000000000000000000000000000000000000),((82407619584658202042707991:ℚ)/155648000000000000000000000)⟩
theorem valid18 : Valid source16 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source16 nn0 nn1 Qcell ((4329:ℚ)/6400) ((8677:ℚ)/12800) :=
  cell_of_packet source16 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((8677:ℚ)/12800),((1087:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((7263482849:ℚ)/10000000000),((7353040873:ℚ)/10000000000),((-20267122619:ℚ)/21692500000),((-46044379943:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((2425051423:ℚ)/2500000000),((2480870833:ℚ)/10000000000),((2986946669:ℚ)/10000000000),((3728048500746003320912758486510100854781714389506489661013:ℚ)/58892223858702551040649414062500000000000000000000000000000),((82443294151670305703067311:ℚ)/155648000000000000000000000)⟩
theorem valid19 : Valid source16 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source16 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1087:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7278338459:ℚ)/10000000000),((3691371171:ℚ)/5000000000),((-10178113513:ℚ)/10870000000),((-46148369213:ℚ)/54587500000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((2919789549:ℚ)/10000000000),((22971412202475356071639206320694789383937514371655595549773:ℚ)/358794947315062016601562500000000000000000000000000000000000),((20628663201254452056822519:ℚ)/38912000000000000000000000)⟩
theorem valid20 : Valid source16 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source16 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((3654024761:ℚ)/5000000000),((741244369:ℚ)/1000000000),((-2044533107:ℚ)/2183500000),((-23178173327:ℚ)/27412500000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((1390378253:ℚ)/5000000000),((22757986561255124442708064228654397697349198098616973839:ℚ)/355577438720866376953125000000000000000000000000000000000),((825860241514648317856799:ℚ)/1556480000000000000000000)⟩
theorem valid21 : Valid source16 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source16 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((7337760381:ℚ)/10000000000),((1867961507:ℚ)/2500000000),((-5155884521:ℚ)/5482500000),((-46564322667:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((658649133:ℚ)/2500000000),((50335176324954187237330082521378196916958337642004251:ℚ)/769415262681884765625000000000000000000000000000000000),((5170550308440187879609591:ℚ)/9728000000000000000000000)⟩
theorem valid22 : Valid source16 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source16 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-15:ℚ)/16),((-7:ℚ)/8),((924647687:ℚ)/1250000000),((7590649319:ℚ)/10000000000),((-20979947957:ℚ)/22120000000),((-5872533809:ℚ)/7031250000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((578858721:ℚ)/2500000000),((222409793235246558385019770596828592757514635500171951:ℚ)/3261452985000000000000000000000000000000000000000000000),((83014518973626941970117199:ℚ)/155648000000000000000000000)⟩
theorem valid23 : Valid source16 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source16 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((7516021387:ℚ)/10000000000),((3854725419:ℚ)/5000000000),((-10668176257:ℚ)/11250000000),((-47812149709:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1487966899:ℚ)/10000000000),((154714384793367846237399056273957387302904043549996476039:ℚ)/2274676666259765625000000000000000000000000000000000000000),((109259231:ℚ)/204800000)⟩
theorem valid24 : Valid source16 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((7634858289:ℚ)/10000000000),((8659808583:ℚ)/10000000000),(-1:ℚ),((-16214669341:ℚ)/21600000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((26775113420825127720440273916425363:ℚ)/291600000000000000000000000000000000),((109259231:ℚ)/204800000)⟩
theorem valid25 : Valid source16 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((8585461689:ℚ)/10000000000),((10560320077:ℚ)/10000000000),(-1:ℚ),((-55298231823:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((296098893279374739776764730468424149:ℚ)/3000000000000000000000000000000000000),((109259231:ℚ)/204800000)⟩
theorem valid26 : Valid source16 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((5243162161:ℚ)/5000000000),((3590230107:ℚ)/2500000000),(-1:ℚ),((-34302135127:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((21125282489068028492326973:ℚ)/190440000000000000000000000),((109259231:ℚ)/204800000)⟩
theorem valid27 : Valid source16 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet27 valid27
private theorem node1_3 :
    CellBound source16 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2079:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source16 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source16 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8449:ℚ)/12800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source16 nn0 nn1 Qcell ((2079:ℚ)/3200) ((8449:ℚ)/12800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((8449:ℚ)/12800) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source16 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source16 nn0 nn1 Qcell ((8449:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source16 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source16 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source16 nn0 nn1 Qcell ((8449:ℚ)/12800) ((4291:ℚ)/6400) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((4291:ℚ)/6400) :=
  cell_join node0_7 node7_14
private theorem node15_17 :
    CellBound source16 nn0 nn1 Qcell ((8601:ℚ)/12800) ((8639:ℚ)/12800) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source16 nn0 nn1 Qcell ((4291:ℚ)/6400) ((8639:ℚ)/12800) :=
  cell_join leaf14 node15_17
private theorem node17_19 :
    CellBound source16 nn0 nn1 Qcell ((8639:ℚ)/12800) ((8677:ℚ)/12800) :=
  cell_join leaf17 leaf18
private theorem node19_21 :
    CellBound source16 nn0 nn1 Qcell ((8677:ℚ)/12800) ((4367:ℚ)/6400) :=
  cell_join leaf19 leaf20
private theorem node17_21 :
    CellBound source16 nn0 nn1 Qcell ((8639:ℚ)/12800) ((4367:ℚ)/6400) :=
  cell_join node17_19 node19_21
private theorem node14_21 :
    CellBound source16 nn0 nn1 Qcell ((4291:ℚ)/6400) ((4367:ℚ)/6400) :=
  cell_join node14_17 node17_21
private theorem node22_24 :
    CellBound source16 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf22 leaf23
private theorem node21_24 :
    CellBound source16 nn0 nn1 Qcell ((4367:ℚ)/6400) ((45:ℚ)/64) :=
  cell_join leaf21 node22_24
private theorem node24_26 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((81:ℚ)/100) :=
  cell_join leaf24 leaf25
private theorem node26_28 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf26 leaf27
private theorem node24_28 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node24_26 node26_28
private theorem node21_28 :
    CellBound source16 nn0 nn1 Qcell ((4367:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node21_24 node24_28
private theorem node14_28 :
    CellBound source16 nn0 nn1 Qcell ((4291:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node14_21 node21_28
private theorem node0_28 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_14 node14_28
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_28
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27]
theorem packet_count : packets.length = 28 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC02
#check @N11Formalization.C450Source16GroupedC02.bound
#print axioms N11Formalization.C450Source16GroupedC02.valid0
#print axioms N11Formalization.C450Source16GroupedC02.valid1
#print axioms N11Formalization.C450Source16GroupedC02.valid2
#print axioms N11Formalization.C450Source16GroupedC02.valid3
#print axioms N11Formalization.C450Source16GroupedC02.valid4
#print axioms N11Formalization.C450Source16GroupedC02.valid5
#print axioms N11Formalization.C450Source16GroupedC02.valid6
#print axioms N11Formalization.C450Source16GroupedC02.valid7
#print axioms N11Formalization.C450Source16GroupedC02.valid8
#print axioms N11Formalization.C450Source16GroupedC02.valid9
#print axioms N11Formalization.C450Source16GroupedC02.valid10
#print axioms N11Formalization.C450Source16GroupedC02.valid11
#print axioms N11Formalization.C450Source16GroupedC02.valid12
#print axioms N11Formalization.C450Source16GroupedC02.valid13
#print axioms N11Formalization.C450Source16GroupedC02.valid14
#print axioms N11Formalization.C450Source16GroupedC02.valid15
#print axioms N11Formalization.C450Source16GroupedC02.valid16
#print axioms N11Formalization.C450Source16GroupedC02.valid17
#print axioms N11Formalization.C450Source16GroupedC02.valid18
#print axioms N11Formalization.C450Source16GroupedC02.valid19
#print axioms N11Formalization.C450Source16GroupedC02.valid20
#print axioms N11Formalization.C450Source16GroupedC02.valid21
#print axioms N11Formalization.C450Source16GroupedC02.valid22
#print axioms N11Formalization.C450Source16GroupedC02.valid23
#print axioms N11Formalization.C450Source16GroupedC02.valid24
#print axioms N11Formalization.C450Source16GroupedC02.valid25
#print axioms N11Formalization.C450Source16GroupedC02.valid26
#print axioms N11Formalization.C450Source16GroupedC02.valid27
#print axioms N11Formalization.C450Source16GroupedC02.bound
#print axioms N11Formalization.C450Source16GroupedC02.endpoint_checks
