import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((3323199637:ℚ)/5000000000),((3418534957:ℚ)/5000000000),((-21689744699:ℚ)/24800000000),((-38401595281:ℚ)/50550000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((5063382819:ℚ)/10000000000),((132169222285135222050508180187543787925009:ℚ)/2030000447400000000000000000000000000000000),((11242718142252691192758763:ℚ)/24320000000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((845663891:ℚ)/1250000000),((1391188653:ℚ)/2000000000),((-8842320571:ℚ)/10110000000),((-9793630583:ℚ)/12875000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((946145317:ℚ)/2000000000),((3479356920699692373484038137876240985855364569603619037:ℚ)/53530088806538085937500000000000000000000000000000000000),((5410945237992551924832449:ℚ)/11673600000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((6884216999:ℚ)/10000000000),((876922281:ℚ)/1250000000),((-5578455967:ℚ)/6437500000),((-79894820987:ℚ)/103950000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((1749959:ℚ)/4000000),((87044060644854681320211086779689410587239325908278333:ℚ)/1396401250530034303665161132812500000000000000000000000),((2116471077722611383262121:ℚ)/4560000000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((6943667793:ℚ)/10000000000),((3537406071:ℚ)/5000000000),((-292491461:ℚ)/337500000),((-80667681309:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((4186452911:ℚ)/10000000000),((68650035399378400578343620841629905249077031557399841:ℚ)/1101643518218994140625000000000000000000000000000000000),((33908668679836724492641001:ℚ)/72960000000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-7:ℚ)/8),((-13:ℚ)/16),((7003117213:ℚ)/10000000000),((710452869:ℚ)/1000000000),((-4525170083:ℚ)/5245000000),((-81440523769:ℚ)/105375000000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((7979339:ℚ)/20000000),((4890432972097237735132464087516581762475094132614022861:ℚ)/80109063954218847656250000000000000000000000000000000000),((1357249405154348186942321:ℚ)/2918400000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((3516420709:ℚ)/5000000000),((3567122489:ℚ)/5000000000),((-7576619141:ℚ)/8781250000),((-40913469217:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((3887755959:ℚ)/10000000000),((14472906562227403428835912511230333466307184041115669245923:ℚ)/237083194926378726959228515625000000000000000000000000000000),((11317934023222964878514627:ℚ)/24320000000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7062565293:ℚ)/10000000000),((7163961007:ℚ)/10000000000),((-45667727049:ℚ)/52925000000),((-82213348809:ℚ)/106325000000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((75664847:ℚ)/200000000),((12788128741669856231595523499465263884582976315531057644080287:ℚ)/209490047799761373291015625000000000000000000000000000000000000),((45301826004011535161590163:ℚ)/97280000000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4253:ℚ)/6400),((341:ℚ)/512),((-7:ℚ)/8),((-13:ℚ)/16),((7092288843:ℚ)/10000000000),((7178818927:ℚ)/10000000000),((-45771732489:ℚ)/53162500000),((-82599754959:ℚ)/106562500000),((195067017:ℚ)/200000000),((2440069189:ℚ)/2500000000),((1112811311:ℚ)/5000000000),((918976601:ℚ)/2500000000),((32991613688677070572948658017361652715544499773410075647:ℚ)/545977778141591613769531250000000000000000000000000000000),((45316871208486756002101523:ℚ)/97280000000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((4253:ℚ)/6400) ((341:ℚ)/512) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((341:ℚ)/512),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((7107150497:ℚ)/10000000000),((7193676783:ℚ)/10000000000),((-45875737481:ℚ)/53281250000),((-82792956461:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((1950670171:ℚ)/2000000000),((2256500263:ℚ)/10000000000),((1810550863:ℚ)/5000000000),((101812599991149795247752527006707513992289620654791543709409:ℚ)/1684867541354298591613769531250000000000000000000000000000000),((135995749733667122510607929:ℚ)/291840000000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((341:ℚ)/512) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((267:ℚ)/400),((8563:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((890251509:ℚ)/1250000000),((450533411:ℚ)/625000000),((-2873733877:ℚ)/3337500000),((-10373269617:ℚ)/13379687500),((9739690061:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((1143344217:ℚ)/5000000000),((3565492727:ℚ)/10000000000),((4289702273615820269761539035150002776249304210428985420673:ℚ)/70987925817664947509765625000000000000000000000000000000000),((177136570754797127457227:ℚ)/380000000000000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((8563:ℚ)/12800) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8563:ℚ)/12800),((4291:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7136873567:ℚ)/10000000000),((1805848077:ℚ)/2500000000),((-11520936539:ℚ)/13379687500),((-83179356371:ℚ)/107275000000),((1216619291:ℚ)/1250000000),((4869845033:ℚ)/5000000000),((1158107867:ℚ)/5000000000),((877260277:ℚ)/2500000000),((26025811239059311099452572558446928216111387136366277443929:ℚ)/430680275843425300233066082000732421875000000000000000000000),((8505376465598666877367169:ℚ)/18240000000000000000000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((8563:ℚ)/12800) ((4291:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4291:ℚ)/6400),((8601:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7151734983:ℚ)/10000000000),((7238249977:ℚ)/10000000000),((-6598249977:ℚ)/7662500000),((-27790851593:ℚ)/35837500000),((1215785143:ℚ)/1250000000),((9732954333:ℚ)/10000000000),((2345108749:ℚ)/10000000000),((172585273:ℚ)/500000000),((5804097492314095173431579736075724644485718872832343153:ℚ)/96045947866771221160888671875000000000000000000000000000),((45377053685755338240441923:ℚ)/97280000000000000000000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell ((4291:ℚ)/6400) ((8601:ℚ)/12800) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((8601:ℚ)/12800),((431:ℚ)/640),((-7:ℚ)/8),((-13:ℚ)/16),((3583298161:ℚ)/5000000000),((1450621517:ℚ)/2000000000),((-3086116873:ℚ)/3583750000),((-41782876093:ℚ)/53875000000),((607479381:ℚ)/625000000),((9726281149:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1696720451:ℚ)/5000000000),((473043108774355482641622582414389592186656188076144497:ℚ)/7827786608503895401954650878906250000000000000000000000),((1815683988917514686064043:ℚ)/3891200000000000000000000)⟩
theorem valid12 : Valid source16 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source16 nn0 nn1 Qcell ((8601:ℚ)/12800) ((431:ℚ)/640) :=
  cell_of_packet source16 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((431:ℚ)/640),((8639:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((3590728791:ℚ)/5000000000),((1816991283:ℚ)/2500000000),((-11598938981:ℚ)/13468750000),((-41879474283:ℚ)/53993750000),((4856560387:ℚ)/5000000000),((9719670101:ℚ)/10000000000),((9604357:ℚ)/40000000),((3334198679:ℚ)/10000000000),((1320440462400706320679339230936829517693415117569311133801:ℚ)/21849990785239338874816894531250000000000000000000000000000),((8513839861513308856284929:ℚ)/18240000000000000000000000)⟩
theorem valid13 : Valid source16 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source16 nn0 nn1 Qcell ((431:ℚ)/640) ((8639:ℚ)/12800) :=
  cell_of_packet source16 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((8639:ℚ)/12800),((4329:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((3598159383:ℚ)/5000000000),((3641411309:ℚ)/5000000000),((-23249879163:ℚ)/26996875000),((-13992023993:ℚ)/18037500000),((2426658193:ℚ)/2500000000),((9713120779:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((81848141:ℚ)/250000000),((12089722177130508680996492637851425208141594133198197306029:ℚ)/200052137907805536836385726928710937500000000000000000000000),((11355548075287962246307947:ℚ)/24320000000000000000000000)⟩
theorem valid14 : Valid source16 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source16 nn0 nn1 Qcell ((8639:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4329:ℚ)/6400),((8677:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7211179873:ℚ)/10000000000),((1824420011:ℚ)/2500000000),((-11650940077:ℚ)/13528125000),((-84145338349:ℚ)/108462500000),((9700205687:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((306851119:ℚ)/1250000000),((401570463:ℚ)/1250000000),((67698198755728863272608874116351934283056395450977208452287:ℚ)/1120208065922148792743682861328125000000000000000000000000000),((2839827427699398710609627:ℚ)/6080000000000000000000000)⟩
theorem valid15 : Valid source16 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source16 nn0 nn1 Qcell ((4329:ℚ)/6400) ((8677:ℚ)/12800) :=
  cell_of_packet source16 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((8677:ℚ)/12800),((1087:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((7226040903:ℚ)/10000000000),((731253741:ℚ)/1000000000),((-4670776187:ℚ)/5423125000),((-84338531739:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((2425051423:ℚ)/2500000000),((2480870833:ℚ)/10000000000),((3150049169:ℚ)/10000000000),((1779554973222196634392996617211293304381819748587817996753:ℚ)/29446111929351275520324707031250000000000000000000000000000),((71766766664500718885339:ℚ)/153600000000000000000000)⟩
theorem valid16 : Valid source16 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source16 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1087:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((3620450929:ℚ)/5000000000),((1468450393:ℚ)/2000000000),((-9383152751:ℚ)/10870000000),((-42265862077:ℚ)/54587500000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((3086311917:ℚ)/10000000000),((7299373821585607964266542045325541488879002911981169516433:ℚ)/119598315771687338867187500000000000000000000000000000000000),((1819295179442498398264963:ℚ)/3891200000000000000000000)⟩
theorem valid17 : Valid source16 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source16 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((7270623543:ℚ)/10000000000),((1842991571:ℚ)/2500000000),((-11780940997:ℚ)/13646875000),((-28306035353:ℚ)/36550000000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((147742549:ℚ)/500000000),((404714463835508626958814245032729537626585861628220389909:ℚ)/6631388051231435388326644897460937500000000000000000000000),((2844529631111168157330667:ℚ)/6080000000000000000000000)⟩
theorem valid18 : Valid source16 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source16 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-7:ℚ)/8),((-13:ℚ)/16),((1825086233:ℚ)/2500000000),((1850420093:ℚ)/2500000000),((-11832940651:ℚ)/13706250000),((-21326121029:ℚ)/27531250000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((563490239:ℚ)/2000000000),((140125194651665032825571166442022912709241454309354686349:ℚ)/2296089864675908088684082031250000000000000000000000000000),((2846410587148425652940363:ℚ)/6080000000000000000000000)⟩
theorem valid19 : Valid source16 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source16 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source16 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((7330066027:ℚ)/10000000000),((928924279:ℚ)/1250000000),((-5942469953:ℚ)/6882812500),((-12241551193:ℚ)/15800000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2673196319:ℚ)/10000000000),((232842905576194684700147121489257130309780544714938779101:ℚ)/3815515928579270839691162109375000000000000000000000000000),((37477520870779619484593:ℚ)/80000000000000000000000)⟩
theorem valid20 : Valid source16 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source16 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((7359786833:ℚ)/10000000000),((1872705319:ℚ)/2500000000),((-1712705319:ℚ)/1975000000),((-86077228829:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((630227279:ℚ)/2500000000),((186289981455339548853896175435650171664691836087289725313:ℚ)/2995645861912841796875000000000000000000000000000000000000),((2852053713722786767346307:ℚ)/6080000000000000000000000)⟩
theorem valid21 : Valid source16 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-7:ℚ)/8),((-13:ℚ)/16),((3709613797:ℚ)/5000000000),((94378093:ℚ)/125000000),((-604646651:ℚ)/697187500),((-43424979361:ℚ)/56250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((546360001:ℚ)/2500000000),((1932168036313170547910498932852626735032142875897:ℚ)/31079550883769989013671875000000000000000000000000),((375765265164577847177:ℚ)/800000000000000000000)⟩
theorem valid22 : Valid source16 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source16 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source16 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((3739333621:ℚ)/5000000000),((29957411:ℚ)/39062500),((-384403754:ℚ)/439453125),((-43811337073:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1789273469:ℚ)/10000000000),((143101488912892246456345541674629214705493567029162263673:ℚ)/2221363931894302368164062500000000000000000000000000000000),((60188759:ℚ)/128000000)⟩
theorem valid23 : Valid source16 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((474846457:ℚ)/625000000),((4309894997:ℚ)/5000000000),((-2539024089:ℚ)/2600000000),((-5573003941:ℚ)/8100000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),((127134937:ℚ)/5000000000),((5489312691374919707067715074987291835825669360584833:ℚ)/57750468750000000000000000000000000000000000000000000),((60188759:ℚ)/128000000)⟩
theorem valid24 : Valid source16 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((427420931:ℚ)/500000000),((5260390181:ℚ)/5000000000),(-1:ℚ),((-5076472103:ℚ)/8000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3168385898268846626796779821345829:ℚ)/30000000000000000000000000000000000),((60188759:ℚ)/128000000)⟩
theorem valid25 : Valid source16 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((10449669827:ℚ)/10000000000),((14321942599:ℚ)/10000000000),(-1:ℚ),((-126245707751:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((355804526394429794191079837:ℚ)/3047040000000000000000000000),((60188759:ℚ)/128000000)⟩
theorem valid26 : Valid source16 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet26 valid26
private theorem node1_3 :
    CellBound source16 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2079:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source16 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source16 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source16 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source16 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source16 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source16 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_6 node6_13
private theorem node14_16 :
    CellBound source16 nn0 nn1 Qcell ((8639:ℚ)/12800) ((8677:ℚ)/12800) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source16 nn0 nn1 Qcell ((431:ℚ)/640) ((8677:ℚ)/12800) :=
  cell_join leaf13 node14_16
private theorem node16_18 :
    CellBound source16 nn0 nn1 Qcell ((8677:ℚ)/12800) ((4367:ℚ)/6400) :=
  cell_join leaf16 leaf17
private theorem node18_20 :
    CellBound source16 nn0 nn1 Qcell ((4367:ℚ)/6400) ((881:ℚ)/1280) :=
  cell_join leaf18 leaf19
private theorem node16_20 :
    CellBound source16 nn0 nn1 Qcell ((8677:ℚ)/12800) ((881:ℚ)/1280) :=
  cell_join node16_18 node18_20
private theorem node13_20 :
    CellBound source16 nn0 nn1 Qcell ((431:ℚ)/640) ((881:ℚ)/1280) :=
  cell_join node13_16 node16_20
private theorem node21_23 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound source16 nn0 nn1 Qcell ((881:ℚ)/1280) ((45:ℚ)/64) :=
  cell_join leaf20 node21_23
private theorem node23_25 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((81:ℚ)/100) :=
  cell_join leaf23 leaf24
private theorem node25_27 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf25 leaf26
private theorem node23_27 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node23_25 node25_27
private theorem node20_27 :
    CellBound source16 nn0 nn1 Qcell ((881:ℚ)/1280) ((69:ℚ)/50) :=
  cell_join node20_23 node23_27
private theorem node13_27 :
    CellBound source16 nn0 nn1 Qcell ((431:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node13_20 node20_27
private theorem node0_27 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_13 node13_27
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_27
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26]
theorem packet_count : packets.length = 27 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC03
#check @N11Formalization.C450Source16GroupedC03.bound
#print axioms N11Formalization.C450Source16GroupedC03.valid0
#print axioms N11Formalization.C450Source16GroupedC03.valid1
#print axioms N11Formalization.C450Source16GroupedC03.valid2
#print axioms N11Formalization.C450Source16GroupedC03.valid3
#print axioms N11Formalization.C450Source16GroupedC03.valid4
#print axioms N11Formalization.C450Source16GroupedC03.valid5
#print axioms N11Formalization.C450Source16GroupedC03.valid6
#print axioms N11Formalization.C450Source16GroupedC03.valid7
#print axioms N11Formalization.C450Source16GroupedC03.valid8
#print axioms N11Formalization.C450Source16GroupedC03.valid9
#print axioms N11Formalization.C450Source16GroupedC03.valid10
#print axioms N11Formalization.C450Source16GroupedC03.valid11
#print axioms N11Formalization.C450Source16GroupedC03.valid12
#print axioms N11Formalization.C450Source16GroupedC03.valid13
#print axioms N11Formalization.C450Source16GroupedC03.valid14
#print axioms N11Formalization.C450Source16GroupedC03.valid15
#print axioms N11Formalization.C450Source16GroupedC03.valid16
#print axioms N11Formalization.C450Source16GroupedC03.valid17
#print axioms N11Formalization.C450Source16GroupedC03.valid18
#print axioms N11Formalization.C450Source16GroupedC03.valid19
#print axioms N11Formalization.C450Source16GroupedC03.valid20
#print axioms N11Formalization.C450Source16GroupedC03.valid21
#print axioms N11Formalization.C450Source16GroupedC03.valid22
#print axioms N11Formalization.C450Source16GroupedC03.valid23
#print axioms N11Formalization.C450Source16GroupedC03.valid24
#print axioms N11Formalization.C450Source16GroupedC03.valid25
#print axioms N11Formalization.C450Source16GroupedC03.valid26
#print axioms N11Formalization.C450Source16GroupedC03.bound
#print axioms N11Formalization.C450Source16GroupedC03.endpoint_checks
