import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((1360329919:ℚ)/2000000000),((7006869397:ℚ)/10000000000),((-42968085779:ℚ)/49600000000),((-5041429649:ℚ)/6740000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4624684747:ℚ)/10000000000),((421239947431023350633740468402772776961729:ℚ)/3464534096896000000000000000000000000000000),((1225037184155885701886488219:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((3460349109:ℚ)/5000000000),((7066355201:ℚ)/10000000000),((-14461495469:ℚ)/16850000000),((-38584538417:ℚ)/51025000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((33282719:ℚ)/78125000),((53510149840785520739326721787540534390053891076505809469:ℚ)/460637250340332031250000000000000000000000000000000000000),((1227255260985455267282888691:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((1396043669:ℚ)/2000000000),((1781459739:ℚ)/2500000000),((-10950218173:ℚ)/12756250000),((-15588567697:ℚ)/20600000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((4066531179:ℚ)/10000000000),((15983912114805175599386714176068026709160446453059692920207:ℚ)/137633303156874084472656250000000000000000000000000000000000),((230526310322396354636795633:ℚ)/346560000000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((879966973:ℚ)/1250000000),((3577790041:ℚ)/5000000000),((-22004530287:ℚ)/25750000000),((-9839570649:ℚ)/12934375000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((3863753683:ℚ)/10000000000),((2075703434825813464496147380122361815048245490717247179384327:ℚ)/18281110353874023437500000000000000000000000000000000000000000),((852204274007852938075211:ℚ)/1280000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((88368669:ℚ)/125000000),((7185320717:ℚ)/10000000000),((-44217245019:ℚ)/51737500000),((-988792697:ℚ)/1299375000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((1879242351:ℚ)/5000000000),((240808284271716159633053565221941150206474884987844858172171:ℚ)/2120834274913998413085937500000000000000000000000000000000000),((1231692368368906190879937899:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2079:ℚ)/3200),((1667:ℚ)/2560),((-7:ℚ)/8),((-13:ℚ)/16),((7099250611:ℚ)/10000000000),((1800047713:ℚ)/2500000000),((-11080333991:ℚ)/12993750000),((-79490257943:ℚ)/104187500000),((4912776717:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((935297099:ℚ)/5000000000),((73006633:ℚ)/200000000),((1069509393787124858320822211489842258620972075822011818613959:ℚ)/9525652751978939437866210937500000000000000000000000000000000),((77015443550713501550755379:ℚ)/115520000000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1667:ℚ)/2560) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1667:ℚ)/2560),((4177:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((3557064459:ℚ)/5000000000),((7215060867:ℚ)/10000000000),((-44425426069:ℚ)/52093750000),((-39841837967:ℚ)/52212500000),((4909016731:ℚ)/5000000000),((9825553439:ℚ)/10000000000),((382121547:ℚ)/2000000000),((3595092363:ℚ)/10000000000),((432724353333470052148054168726292233551098690007529120620101829:ℚ)/3853947915681878423690795898437500000000000000000000000000000000),((3698405536129352191633518497:ℚ)/5544960000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((1667:ℚ)/2560) ((4177:ℚ)/6400) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4177:ℚ)/6400),((8373:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7129007067:ℚ)/10000000000),((3614965381:ℚ)/5000000000),((-22264757667:ℚ)/26106250000),((-79877091871:ℚ)/104662500000),((4905290651:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((194946007:ℚ)/1000000000),((707805917:ℚ)/2000000000),((218844894509429516756898811686192846315947162101644744228618923:ℚ)/1949017265046141836929321289062500000000000000000000000000000000),((308339153515853692778513851:ℚ)/462080000000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8373:ℚ)/12800) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((8373:ℚ)/12800),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((357194253:ℚ)/500000000),((7244800539:ℚ)/10000000000),((-44633603773:ℚ)/52331250000),((-4003525289:ℚ)/5245000000),((4901598247:ℚ)/5000000000),((9810581307:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3482103471:ℚ)/10000000000),((9222924299206879628388231671701388675660067445570860066200599:ℚ)/82135910038266234970092773437500000000000000000000000000000000),((3701734208839001798291310833:ℚ)/5544960000000000000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((8373:ℚ)/12800) ((1049:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1049:ℚ)/1600),((8411:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((447422681:ℚ)/625000000),((3629835099:ℚ)/5000000000),((-22368845693:ℚ)/26225000000),((-5016494853:ℚ)/6571093750),((9795878581:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((1011977397:ℚ)/5000000000),((428033863:ℚ)/1250000000),((895512777011443179597990382303999468458215381589138355747602933:ℚ)/7974836242399778222656250000000000000000000000000000000000000000),((925849659018466960139612273:ℚ)/1386240000000000000000000000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8411:ℚ)/12800) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8411:ℚ)/12800),((843:ℚ)/1280),((-7:ℚ)/8),((-13:ℚ)/16),((7173640579:ℚ)/10000000000),((363726987:ℚ)/500000000),((-2242088909:ℚ)/2628437500),((-80457327527:ℚ)/105375000000),((978862711:ℚ)/1000000000),((4897939293:ℚ)/5000000000),((2059717253:ℚ)/10000000000),((3365485073:ℚ)/10000000000),((2830363496089713533756455483186789697342429839586594587:ℚ)/25204503818531311690807342529296875000000000000000000000),((9262657810012568877755537:ℚ)/13862400000000000000000000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell ((8411:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((843:ℚ)/1280),((8449:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((1797129527:ℚ)/2500000000),((1457881833:ℚ)/2000000000),((-8989172831:ℚ)/10537500000),((-20162683851:ℚ)/26403125000),((4890720817:ℚ)/5000000000),((1957725423:ℚ)/2000000000),((83782417:ℚ)/400000000),((3305695059:ℚ)/10000000000),((697913881441724459186582336490021430371986626325337875067331:ℚ)/6214756459341329956054687500000000000000000000000000000000000),((148269106905229561588597097:ℚ)/221798400000000000000000000)⟩
theorem valid11 : Valid source21 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source21 nn0 nn1 Qcell ((843:ℚ)/1280) ((8449:ℚ)/12800) :=
  cell_of_packet source21 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((8449:ℚ)/12800),((2117:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((1800848871:ℚ)/2500000000),((292171139:ℚ)/400000000),((-1801997973:ℚ)/2112250000),((-20211035323:ℚ)/26462500000),((9774321709:ℚ)/10000000000),((9781441639:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1622422641:ℚ)/5000000000),((4234972997739710457130497253806417877834345303338412254571:ℚ)/37710270678850334277343750000000000000000000000000000000000),((1977809217159020845942411:ℚ)/2957312000000000000000000)⟩
theorem valid12 : Valid source21 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source21 nn0 nn1 Qcell ((8449:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2117:ℚ)/3200),((8487:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7218272709:ℚ)/10000000000),((731914767:ℚ)/1000000000),((-4515403369:ℚ)/5292500000),((-81037545217:ℚ)/106087500000),((9767266893:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((2161672951:ℚ)/10000000000),((795718721:ℚ)/2500000000),((832784049970235660051473990226239628598643377721628829277769:ℚ)/7415296353039231738281250000000000000000000000000000000000000),((37100569526305906027898297:ℚ)/55449600000000000000000000)⟩
theorem valid13 : Valid source21 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source21 nn0 nn1 Qcell ((2117:ℚ)/3200) ((8487:ℚ)/12800) :=
  cell_of_packet source21 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((8487:ℚ)/12800),((4253:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((904143723:ℚ)/1250000000),((7334016751:ℚ)/10000000000),((-45258117257:ℚ)/53043750000),((-10153868399:ℚ)/13290625000),((9760276751:ℚ)/10000000000),((4883633449:ℚ)/5000000000),((438804929:ℚ)/2000000000),((779929253:ℚ)/2500000000),((5135272235248998595268789654999662663792581322410327549306577:ℚ)/45724301016378758239746093750000000000000000000000000000000000),((1237240561371089422820158291:ℚ)/1848320000000000000000000000)⟩
theorem valid14 : Valid source21 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source21 nn0 nn1 Qcell ((8487:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_of_packet source21 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4253:ℚ)/6400),((341:ℚ)/512),((-7:ℚ)/8),((-13:ℚ)/16),((7248026709:ℚ)/10000000000),((7348885719:ℚ)/10000000000),((-45362200033:ℚ)/53162500000),((-81424347217:ℚ)/106562500000),((195067017:ℚ)/200000000),((2440069189:ℚ)/2500000000),((1112811311:ℚ)/5000000000),((3055297953:ℚ)/10000000000),((4905615252042521724383144359831267560475423139286187725417:ℚ)/43678222251327329101562500000000000000000000000000000000000),((3713386476731466625029822953:ℚ)/5544960000000000000000000000)⟩
theorem valid15 : Valid source21 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source21 nn0 nn1 Qcell ((4253:ℚ)/6400) ((341:ℚ)/512) :=
  cell_of_packet source21 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((341:ℚ)/512),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((3631451743:ℚ)/5000000000),((294550183:ℚ)/400000000),((-1818651281:ℚ)/2131250000),((-13602957553:ℚ)/17800000000),((4873244381:ℚ)/5000000000),((1950670171:ℚ)/2000000000),((2256500263:ℚ)/10000000000),((29895361:ℚ)/100000000),((3364213315482375740007384236418144322990917393867208651:ℚ)/29953200735187530517578125000000000000000000000000000000),((1981360709650920041103299:ℚ)/2957312000000000000000000)⟩
theorem valid16 : Valid source21 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source21 nn0 nn1 Qcell ((341:ℚ)/512) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((1455556023:ℚ)/2000000000),((462093247:ℚ)/625000000),((-2854652729:ℚ)/3337500000),((-16362228299:ℚ)/21455000000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((2922340727:ℚ)/10000000000),((361416791706548884036643075904147847391731423485333296101:ℚ)/3183182956341361999511718750000000000000000000000000000000),((4841642216362284360373619:ℚ)/7220000000000000000000000)⟩
theorem valid17 : Valid source21 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source21 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-7:ℚ)/8),((-13:ℚ)/16),((913441617:ℚ)/1250000000),((927903611:ℚ)/1250000000),((-5735325277:ℚ)/6704687500),((-10274741021:ℚ)/13468750000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2783231587:ℚ)/10000000000),((155192255005450423897715489844988346364985213904543786907:ℚ)/1366879449153238069266080856323242187500000000000000000000),((19383913330646803666004411:ℚ)/28880000000000000000000000)⟩
theorem valid18 : Valid source21 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source21 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source21 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((7337285179:ℚ)/10000000000),((374135073:ℚ)/500000000),((-2314945511:ℚ)/2693750000),((-82584707327:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((164812277:ℚ)/625000000),((16735703483096067948696336361599441459134962004485017026671:ℚ)/144348065510374450683593750000000000000000000000000000000000),((9320930934713522233096217:ℚ)/13862400000000000000000000)⟩
theorem valid19 : Valid source21 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source21 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((7396787963:ℚ)/10000000000),((1900410391:ℚ)/2500000000),((-11782872737:ℚ)/13587500000),((-83358243519:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2317690239:ℚ)/10000000000),((737734929759997462871534938005067518825993586168920018897:ℚ)/6115512927416229248046875000000000000000000000000000000000),((86369193:ℚ)/128000000)⟩
theorem valid20 : Valid source21 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((7515786923:ℚ)/10000000000),((3919751393:ℚ)/5000000000),((-24398259751:ℚ)/27650000000),((-84905229999:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1490046461:ℚ)/10000000000),((50051961874251581638064791564084289317728182094426112811513:ℚ)/385957477374218750000000000000000000000000000000000000000000),((86369193:ℚ)/128000000)⟩
theorem valid21 : Valid source21 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((193843999:ℚ)/250000000),((1758147089:ℚ)/2000000000),((-11091029623:ℚ)/11440000000),((-2199971987:ℚ)/3240000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((931431216024609212353224587488842114486505619987188528829:ℚ)/5116192567200000000000000000000000000000000000000000000000),((86369193:ℚ)/128000000)⟩
theorem valid22 : Valid source21 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((8705374023:ℚ)/10000000000),((2673124297:ℚ)/2500000000),(-1:ℚ),((-100369862299:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((6587327979675638830831428688769553393:ℚ)/32000000000000000000000000000000000000),((86369193:ℚ)/128000000)⟩
theorem valid23 : Valid source21 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((10607680489:ℚ)/10000000000),((14494564149:ℚ)/10000000000),(-1:ℚ),((-125099846357:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((5563495008645366633178807867:ℚ)/24376320000000000000000000000),((86369193:ℚ)/128000000)⟩
theorem valid24 : Valid source21 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet24 valid24
private theorem node1_3 :
    CellBound source21 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source21 nn0 nn1 Qcell ((4139:ℚ)/6400) ((1667:ℚ)/2560) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source21 nn0 nn1 Qcell ((103:ℚ)/160) ((1667:ℚ)/2560) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1667:ℚ)/2560) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source21 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source21 nn0 nn1 Qcell ((1667:ℚ)/2560) ((1049:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source21 nn0 nn1 Qcell ((8411:ℚ)/12800) ((8449:ℚ)/12800) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source21 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8449:ℚ)/12800) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source21 nn0 nn1 Qcell ((1667:ℚ)/2560) ((8449:ℚ)/12800) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((8449:ℚ)/12800) :=
  cell_join node0_6 node6_12
private theorem node13_15 :
    CellBound source21 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source21 nn0 nn1 Qcell ((8449:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_join leaf12 node13_15
private theorem node16_18 :
    CellBound source21 nn0 nn1 Qcell ((341:ℚ)/512) ((4291:ℚ)/6400) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source21 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join leaf15 node16_18
private theorem node12_18 :
    CellBound source21 nn0 nn1 Qcell ((8449:ℚ)/12800) ((4291:ℚ)/6400) :=
  cell_join node12_15 node15_18
private theorem node19_21 :
    CellBound source21 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source21 nn0 nn1 Qcell ((4291:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join leaf18 node19_21
private theorem node21_23 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf21 leaf22
private theorem node23_25 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf23 leaf24
private theorem node21_25 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node21_23 node23_25
private theorem node18_25 :
    CellBound source21 nn0 nn1 Qcell ((4291:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node18_21 node21_25
private theorem node12_25 :
    CellBound source21 nn0 nn1 Qcell ((8449:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node12_18 node18_25
private theorem node0_25 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_12 node12_25
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_25
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24]
theorem packet_count : packets.length = 25 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC03
#check @N11Formalization.C450Source21GroupedC03.bound
#print axioms N11Formalization.C450Source21GroupedC03.valid0
#print axioms N11Formalization.C450Source21GroupedC03.valid1
#print axioms N11Formalization.C450Source21GroupedC03.valid2
#print axioms N11Formalization.C450Source21GroupedC03.valid3
#print axioms N11Formalization.C450Source21GroupedC03.valid4
#print axioms N11Formalization.C450Source21GroupedC03.valid5
#print axioms N11Formalization.C450Source21GroupedC03.valid6
#print axioms N11Formalization.C450Source21GroupedC03.valid7
#print axioms N11Formalization.C450Source21GroupedC03.valid8
#print axioms N11Formalization.C450Source21GroupedC03.valid9
#print axioms N11Formalization.C450Source21GroupedC03.valid10
#print axioms N11Formalization.C450Source21GroupedC03.valid11
#print axioms N11Formalization.C450Source21GroupedC03.valid12
#print axioms N11Formalization.C450Source21GroupedC03.valid13
#print axioms N11Formalization.C450Source21GroupedC03.valid14
#print axioms N11Formalization.C450Source21GroupedC03.valid15
#print axioms N11Formalization.C450Source21GroupedC03.valid16
#print axioms N11Formalization.C450Source21GroupedC03.valid17
#print axioms N11Formalization.C450Source21GroupedC03.valid18
#print axioms N11Formalization.C450Source21GroupedC03.valid19
#print axioms N11Formalization.C450Source21GroupedC03.valid20
#print axioms N11Formalization.C450Source21GroupedC03.valid21
#print axioms N11Formalization.C450Source21GroupedC03.valid22
#print axioms N11Formalization.C450Source21GroupedC03.valid23
#print axioms N11Formalization.C450Source21GroupedC03.valid24
#print axioms N11Formalization.C450Source21GroupedC03.bound
#print axioms N11Formalization.C450Source21GroupedC03.endpoint_checks
