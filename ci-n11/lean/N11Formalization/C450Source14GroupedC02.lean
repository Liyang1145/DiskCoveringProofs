import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((1653910907:ℚ)/2500000000),((850457309:ℚ)/1250000000),((-2359371927:ℚ)/2480000000),((-3512458783:ℚ)/4212500000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((643276011:ℚ)/1250000000),((74958392627758563905389942180993609358343:ℚ)/1353333631600000000000000000000000000000000),((55712070532560984299769:ℚ)/128000000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((1346895111:ℚ)/2000000000),((865307037:ℚ)/1250000000),((-801307037:ℚ)/842500000),((-8596265777:ℚ)/10300000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((481901591:ℚ)/1000000000),((136813970160027297066976710033766621021273081724344507:ℚ)/2478244852154541015625000000000000000000000000000000000),((20172893538673353875899041:ℚ)/46208000000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((856663057:ℚ)/1250000000),((872731819:ℚ)/1250000000),((-2426195457:ℚ)/2575000000),((-608515711:ℚ)/721875000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((4469938897:ℚ)/10000000000),((18580308681270365499766575947031406968006852635179569:ℚ)/353065402603149414062500000000000000000000000000000000),((20203314695640214153568529:ℚ)/46208000000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((6912717823:ℚ)/10000000000),((7041252387:ℚ)/10000000000),((-932750341:ℚ)/990000000),((-44229024761:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((2142763501:ℚ)/5000000000),((10631903881801822014882501605295866273332809115581054947:ℚ)/202219316268750000000000000000000000000000000000000000000),((1294959228164930114388196641:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-15:ℚ)/16),((-7:ℚ)/8),((1394426099:ℚ)/2000000000),((7070951149:ℚ)/10000000000),((-19676853447:ℚ)/20980000000),((-8928982693:ℚ)/10537500000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((409335261:ℚ)/1000000000),((702058725994499051165957848299263842887259137258864960172291:ℚ)/13671946914853350000000000000000000000000000000000000000000000),((1295932822163067356033578689:ℚ)/2957312000000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7001836577:ℚ)/10000000000),((7100649811:ℚ)/10000000000),((-6588649811:ℚ)/7025000000),((-44852856039:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((3994004959:ℚ)/10000000000),((59820611428942526219016951841978974380705412857738472576167:ℚ)/1165311319702136718750000000000000000000000000000000000000000),((1296906449731671413578875969:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7031542491:ℚ)/10000000000),((7130348373:ℚ)/10000000000),((-19855045119:ℚ)/21170000000),((-45060797437:ℚ)/53162500000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((778452471:ℚ)/2000000000),((13760995082251051328001424653639324333002355657342495553549881:ℚ)/268147261183694557812500000000000000000000000000000000000000000),((1297880110870370061813777681:ℚ)/2957312000000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4253:ℚ)/6400),((341:ℚ)/512),((-15:ℚ)/16),((-7:ℚ)/8),((88265603:ℚ)/125000000),((7145197617:ℚ)/10000000000),((-19899592851:ℚ)/21265000000),((-565859221:ℚ)/666015625),((195067017:ℚ)/200000000),((2440069189:ℚ)/2500000000),((1112811311:ℚ)/5000000000),((3787931341:ℚ)/10000000000),((22155642655641973059245261620599635210476041584854009010949:ℚ)/436782222513273291015625000000000000000000000000000000000000),((1298366954044781553117334521:ℚ)/2957312000000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((4253:ℚ)/6400) ((341:ℚ)/512) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((341:ℚ)/512),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((3538050527:ℚ)/5000000000),((1790011709:ℚ)/2500000000),((-4986035127:ℚ)/5328125000),((-22686353689:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((1950670171:ℚ)/2000000000),((2256500263:ℚ)/10000000000),((3734727449:ℚ)/10000000000),((4143255367581422041590317395002728119120770952164358201:ℚ)/81690547459602355957031250000000000000000000000000000000),((81178362850723608036125409:ℚ)/184832000000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((341:ℚ)/512) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((267:ℚ)/400),((8563:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7090953827:ℚ)/10000000000),((224215501:ℚ)/312500000),((-208215501:ℚ)/222500000),((-45476676789:ℚ)/53518750000),((9739690061:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((1143344217:ℚ)/5000000000),((368079133:ℚ)/1000000000),((256001587014865179653291730798348669963071967426916249059:ℚ)/5048030280367285156250000000000000000000000000000000000000),((1268887368785436137429889:ℚ)/2888000000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((8563:ℚ)/12800) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8563:ℚ)/12800),((4291:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7105806561:ℚ)/10000000000),((7189745203:ℚ)/10000000000),((-20033235609:ℚ)/21407500000),((-45580645927:ℚ)/53637500000),((1216619291:ℚ)/1250000000),((4869845033:ℚ)/5000000000),((1158107867:ℚ)/5000000000),((1813045121:ℚ)/5000000000),((14312211309455983278926255173407228967252745558883779318801439:ℚ)/282250625576747204760742187500000000000000000000000000000000000),((1299827534053289590987644801:ℚ)/2957312000000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((8563:ℚ)/12800) ((4291:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4291:ℚ)/6400),((8601:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((3560329627:ℚ)/5000000000),((144091887:ℚ)/200000000),((-401555661:ℚ)/429100000),((-7614102463:ℚ)/8959375000),((1215785143:ℚ)/1250000000),((9732954333:ℚ)/10000000000),((2345108749:ℚ)/10000000000),((892647243:ℚ)/2500000000),((93161931257341974230573842063133312070316019876107611:ℚ)/1837448734564318750000000000000000000000000000000000000),((520125764358131469043641:ℚ)/1182924800000000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((4291:ℚ)/6400) ((8601:ℚ)/12800) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((8601:ℚ)/12800),((431:ℚ)/640),((-15:ℚ)/16),((-7:ℚ)/8),((1783877977:ℚ)/2500000000),((7219443473:ℚ)/10000000000),((-6707443473:ℚ)/7167500000),((-11447145839:ℚ)/13468750000),((607479381:ℚ)/625000000),((9726281149:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((175712477:ℚ)/500000000),((21672681100625458862557140617867798633788824418215559713063:ℚ)/427501519312426074218750000000000000000000000000000000000000),((1300801296162359183120817081:ℚ)/2957312000000000000000000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((8601:ℚ)/12800) ((431:ℚ)/640) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((431:ℚ)/640),((8639:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7150364523:ℚ)/10000000000),((7234292573:ℚ)/10000000000),((-20166877719:ℚ)/21550000000),((-45892551661:ℚ)/53993750000),((4856560387:ℚ)/5000000000),((9719670101:ℚ)/10000000000),((9604357:ℚ)/40000000),((691406181:ℚ)/2000000000),((1451737801615093333193766713947777283033345475463228312662747:ℚ)/28639219922028906250000000000000000000000000000000000000000000),((1301288189887126209758312481:ℚ)/2957312000000000000000000000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell ((431:ℚ)/640) ((8639:ℚ)/12800) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((8639:ℚ)/12800),((4329:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((3582608549:ℚ)/5000000000),((7249141649:ℚ)/10000000000),((-20211424947:ℚ)/21597500000),((-1769096911:ℚ)/2081250000),((2426658193:ℚ)/2500000000),((9713120779:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((849722151:ℚ)/2500000000),((117960605789536378783157663878209675420628795853696493042791:ℚ)/2327328445548984082031250000000000000000000000000000000000000),((3606025185697497432932049:ℚ)/8192000000000000000000000)⟩
theorem valid14 : Valid source14 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source14 nn0 nn1 Qcell ((8639:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4329:ℚ)/6400),((8677:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((1436013927:ℚ)/2000000000),((3631995351:ℚ)/5000000000),((-3375995351:ℚ)/3607500000),((-9220097489:ℚ)/10846250000),((9700205687:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((306851119:ℚ)/1250000000),((834943581:ℚ)/2500000000),((3358856165579120453452710826878407809424796818990742051926627:ℚ)/66276487882469532128906250000000000000000000000000000000000000),((325565500661029150454155689:ℚ)/739328000000000000000000000)⟩
theorem valid15 : Valid source14 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source14 nn0 nn1 Qcell ((4329:ℚ)/6400) ((8677:ℚ)/12800) :=
  cell_of_packet source14 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((8677:ℚ)/12800),((1087:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((7194922133:ℚ)/10000000000),((7278839731:ℚ)/10000000000),((-20300519193:ℚ)/21692500000),((-46204454931:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((2425051423:ℚ)/2500000000),((2480870833:ℚ)/10000000000),((655927089:ℚ)/2000000000),((238744156116222085489348147660852221050634385702781310965943:ℚ)/4711377908696204083251953125000000000000000000000000000000000),((1302748921676251875518668929:ℚ)/2957312000000000000000000000)⟩
theorem valid16 : Valid source14 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source14 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1087:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((1087:ℚ)/1600),((1743:ℚ)/2560),((-15:ℚ)/16),((-7:ℚ)/8),((7209774593:ℚ)/10000000000),((3646844369:ℚ)/5000000000),((-10172533107:ℚ)/10870000000),((-185977599:ℚ)/218750000),((9687532673:ℚ)/10000000000),((2423459781:ℚ)/2500000000),((2506424897:ℚ)/10000000000),((1609207231:ℚ)/5000000000),((177944547258005066107177919262315096603247607872005339:ℚ)/3511936922265625000000000000000000000000000000000000000),((325808962299685549613475129:ℚ)/739328000000000000000000000)⟩
theorem valid17 : Valid source14 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1743:ℚ)/2560) :=
  cell_of_packet source14 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1743:ℚ)/2560),((4367:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((1444925403:ℚ)/2000000000),((3654268861:ℚ)/5000000000),((-3398268861:ℚ)/3631250000),((-9282477821:ℚ)/10917500000),((2420321489:ℚ)/2500000000),((4843766339:ℚ)/5000000000),((2531487941:ℚ)/10000000000),((3156048333:ℚ)/10000000000),((10326383314784118715414582554217754089255506409682862308373:ℚ)/203824703411448287963867187500000000000000000000000000000000),((325930696294688442823398369:ℚ)/739328000000000000000000000)⟩
theorem valid18 : Valid source14 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source14 nn0 nn1 Qcell ((1743:ℚ)/2560) ((4367:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((4367:ℚ)/6400),((8753:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((36197397:ℚ)/50000000),((7323386683:ℚ)/10000000000),((-20434160049:ℚ)/21835000000),((-232581779:ℚ)/273531250),((483754929:ℚ)/500000000),((9681285961:ℚ)/10000000000),((639018949:ℚ)/2500000000),((618493541:ℚ)/2000000000),((22956512875182228251912795235054825472995158092713690936929949:ℚ)/453169609937786560156250000000000000000000000000000000000000000),((1304209729616243789138852721:ℚ)/2957312000000000000000000000)⟩
theorem valid19 : Valid source14 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source14 nn0 nn1 Qcell ((4367:ℚ)/6400) ((8753:ℚ)/12800) :=
  cell_of_packet source14 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((8753:ℚ)/12800),((2193:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((3627165873:ℚ)/5000000000),((7338235621:ℚ)/10000000000),((-20478706863:ℚ)/21882500000),((-23310161111:ℚ)/27412500000),((4834485079:ℚ)/5000000000),((1935019717:ℚ)/2000000000),((2580203419:ℚ)/10000000000),((3027596001:ℚ)/10000000000),((12512296735480937195609924942973693714230686887259550872883:ℚ)/247023293265614542968750000000000000000000000000000000000000),((1304696682511169447157084849:ℚ)/2957312000000000000000000000)⟩
theorem valid20 : Valid source14 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source14 nn0 nn1 Qcell ((8753:ℚ)/12800) ((2193:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-15:ℚ)/16),((-7:ℚ)/8),((908648007:ℚ)/1250000000),((7367933431:ℚ)/10000000000),((-6855933431:ℚ)/7310000000),((-5840536049:ℚ)/6882812500),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((2961348291:ℚ)/10000000000),((2256274215557327973964395139641909583643242875235658676067:ℚ)/44067205362856250000000000000000000000000000000000000000000),((1305670613771542475362055529:ℚ)/2957312000000000000000000000)⟩
theorem valid21 : Valid source14 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source14 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source14 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((1824722141:ℚ)/2500000000),((462351947:ℚ)/625000000),((-1291055841:ℚ)/1376562500),((-11733054987:ℚ)/13825000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2824335277:ℚ)/10000000000),((36456770666754174128170136186266394973832188368553950613:ℚ)/712229640001463890075683593750000000000000000000000000000),((14138726832578142150441:ℚ)/32000000000000000000000)⟩
theorem valid22 : Valid source14 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source14 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((3664296463:ℚ)/5000000000),((7457026333:ℚ)/10000000000),((-2976439857:ℚ)/3160000000),((-23570075241:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1340262217:ℚ)/5000000000),((51304039289115988902516731465772399988142576288433384539607:ℚ)/981613236031600000000000000000000000000000000000000000000000),((1308592611313887323692284321:ℚ)/2957312000000000000000000000)⟩
theorem valid23 : Valid source14 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-15:ℚ)/16),((-7:ℚ)/8),((3694000609:ℚ)/5000000000),((1879105293:ℚ)/2500000000),((-5253315879:ℚ)/5577500000),((-7926001421:ℚ)/9375000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((236749803:ℚ)/1000000000),((2462350043482137017802213265651145851273832403489103:ℚ)/47148829785156250000000000000000000000000000000000000),((81908798739625844004469761:ℚ)/184832000000000000000000000)⟩
theorem valid24 : Valid source14 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source14 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((1861852237:ℚ)/2500000000),((7635209863:ℚ)/10000000000),((-7123209863:ℚ)/7500000000),((-11992965659:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1003626381:ℚ)/5000000000),((2928346268452765076946799775787093554255231760631937231617:ℚ)/53918261718750000000000000000000000000000000000000000000000),((454737687:ℚ)/1024000000)⟩
theorem valid25 : Valid source14 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-15:ℚ)/16),((-7:ℚ)/8),((945777847:ℚ)/1250000000),((8110352569:ℚ)/10000000000),((-22795057707:ℚ)/22880000000),((-6100444929:ℚ)/7625000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((188630169:ℚ)/2000000000),((4630167116846672631757169886212819953711378201960156726053:ℚ)/69638235180800000000000000000000000000000000000000000000000),((454737687:ℚ)/1024000000)⟩
theorem valid26 : Valid source14 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((8041458191:ℚ)/10000000000),((8585478531:ℚ)/10000000000),((-24220435593:ℚ)/24400000000),((-17376735779:ℚ)/21600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((358868502557892943209770598724291645000199899604951404741:ℚ)/5515638300000000000000000000000000000000000000000000000000),((454737687:ℚ)/1024000000)⟩
theorem valid27 : Valid source14 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((4258332989:ℚ)/5000000000),((10485862681:ℚ)/10000000000),(-1:ℚ),((-27728330923:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((29211731596752175086349022139936131:ℚ)/375000000000000000000000000000000000),((454737687:ℚ)/1024000000)⟩
theorem valid28 : Valid source14 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((10417299633:ℚ)/10000000000),((892894599:ℚ)/625000000),(-1:ℚ),((-68761097431:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((11084448792587535634990961:ℚ)/126960000000000000000000000),((454737687:ℚ)/1024000000)⟩
theorem valid29 : Valid source14 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet29 valid29
private theorem node1_3 :
    CellBound source14 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2079:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source14 nn0 nn1 Qcell ((2079:ℚ)/3200) ((843:ℚ)/1280) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source14 nn0 nn1 Qcell ((843:ℚ)/1280) ((4253:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source14 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((4253:ℚ)/6400) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source14 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source14 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source14 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source14 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source14 nn0 nn1 Qcell ((4291:ℚ)/6400) ((4329:ℚ)/6400) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source14 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4329:ℚ)/6400) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((4329:ℚ)/6400) :=
  cell_join node0_7 node7_15
private theorem node16_18 :
    CellBound source14 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1743:ℚ)/2560) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source14 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1743:ℚ)/2560) :=
  cell_join leaf15 node16_18
private theorem node18_20 :
    CellBound source14 nn0 nn1 Qcell ((1743:ℚ)/2560) ((8753:ℚ)/12800) :=
  cell_join leaf18 leaf19
private theorem node20_22 :
    CellBound source14 nn0 nn1 Qcell ((8753:ℚ)/12800) ((881:ℚ)/1280) :=
  cell_join leaf20 leaf21
private theorem node18_22 :
    CellBound source14 nn0 nn1 Qcell ((1743:ℚ)/2560) ((881:ℚ)/1280) :=
  cell_join node18_20 node20_22
private theorem node15_22 :
    CellBound source14 nn0 nn1 Qcell ((4329:ℚ)/6400) ((881:ℚ)/1280) :=
  cell_join node15_18 node18_22
private theorem node22_24 :
    CellBound source14 nn0 nn1 Qcell ((881:ℚ)/1280) ((2231:ℚ)/3200) :=
  cell_join leaf22 leaf23
private theorem node24_26 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf24 leaf25
private theorem node22_26 :
    CellBound source14 nn0 nn1 Qcell ((881:ℚ)/1280) ((143:ℚ)/200) :=
  cell_join node22_24 node24_26
private theorem node26_28 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_join leaf26 leaf27
private theorem node28_30 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf28 leaf29
private theorem node26_30 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node26_28 node28_30
private theorem node22_30 :
    CellBound source14 nn0 nn1 Qcell ((881:ℚ)/1280) ((69:ℚ)/50) :=
  cell_join node22_26 node26_30
private theorem node15_30 :
    CellBound source14 nn0 nn1 Qcell ((4329:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node15_22 node22_30
private theorem node0_30 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_15 node15_30
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_30
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29]
theorem packet_count : packets.length = 30 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC02
#check @N11Formalization.C450Source14GroupedC02.bound
#print axioms N11Formalization.C450Source14GroupedC02.valid0
#print axioms N11Formalization.C450Source14GroupedC02.valid1
#print axioms N11Formalization.C450Source14GroupedC02.valid2
#print axioms N11Formalization.C450Source14GroupedC02.valid3
#print axioms N11Formalization.C450Source14GroupedC02.valid4
#print axioms N11Formalization.C450Source14GroupedC02.valid5
#print axioms N11Formalization.C450Source14GroupedC02.valid6
#print axioms N11Formalization.C450Source14GroupedC02.valid7
#print axioms N11Formalization.C450Source14GroupedC02.valid8
#print axioms N11Formalization.C450Source14GroupedC02.valid9
#print axioms N11Formalization.C450Source14GroupedC02.valid10
#print axioms N11Formalization.C450Source14GroupedC02.valid11
#print axioms N11Formalization.C450Source14GroupedC02.valid12
#print axioms N11Formalization.C450Source14GroupedC02.valid13
#print axioms N11Formalization.C450Source14GroupedC02.valid14
#print axioms N11Formalization.C450Source14GroupedC02.valid15
#print axioms N11Formalization.C450Source14GroupedC02.valid16
#print axioms N11Formalization.C450Source14GroupedC02.valid17
#print axioms N11Formalization.C450Source14GroupedC02.valid18
#print axioms N11Formalization.C450Source14GroupedC02.valid19
#print axioms N11Formalization.C450Source14GroupedC02.valid20
#print axioms N11Formalization.C450Source14GroupedC02.valid21
#print axioms N11Formalization.C450Source14GroupedC02.valid22
#print axioms N11Formalization.C450Source14GroupedC02.valid23
#print axioms N11Formalization.C450Source14GroupedC02.valid24
#print axioms N11Formalization.C450Source14GroupedC02.valid25
#print axioms N11Formalization.C450Source14GroupedC02.valid26
#print axioms N11Formalization.C450Source14GroupedC02.valid27
#print axioms N11Formalization.C450Source14GroupedC02.valid28
#print axioms N11Formalization.C450Source14GroupedC02.valid29
#print axioms N11Formalization.C450Source14GroupedC02.bound
#print axioms N11Formalization.C450Source14GroupedC02.endpoint_checks
