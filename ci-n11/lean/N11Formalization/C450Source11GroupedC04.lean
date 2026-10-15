import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((6465425729:ℚ)/10000000000),((1351655063:ℚ)/2000000000),((-16419515819:ℚ)/19840000000),((-17796277187:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2767271589:ℚ)/5000000000),((61239557379876860899098687521862284979321079319774707713353:ℚ)/1553462324428800000000000000000000000000000000000000000000000),((1177768440504841514275887:ℚ)/4620800000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((6703094607:ℚ)/10000000000),((1719275471:ℚ)/2500000000),((-20910581123:ℚ)/25750000000),((-18509283821:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4907362263:ℚ)/10000000000),((1086015964501777589756566745404466067483186825026412423811123:ℚ)/29356393640795898437500000000000000000000000000000000000000000),((1843047122937549625886743:ℚ)/7220000000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((1705481113:ℚ)/2500000000),((867064267:ℚ)/1250000000),((-10551835471:ℚ)/13112500000),((-4716443339:ℚ)/6615625000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4564527803:ℚ)/10000000000),((2264255199463602033941617697641408323979058460046418677113159:ℚ)/63150709901076184082031250000000000000000000000000000000000000),((461110332894503403907747:ℚ)/1805000000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((6881338299:ℚ)/10000000000),((279837029:ℚ)/400000000),((-3407481377:ℚ)/4234000000),((-19044014897:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((2191914699:ℚ)/5000000000),((4152826023848473071508748925581897662511714188815136769:ℚ)/115816983581362500000000000000000000000000000000000000000),((47253428094839585336743:ℚ)/184832000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-13:ℚ)/16),((-3:ℚ)/4),((3470375727:ℚ)/5000000000),((7055336669:ℚ)/10000000000),((-85959376697:ℚ)/106800000000),((-9611127181:ℚ)/13468750000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((131121319:ℚ)/312500000),((594320474210350617047421291960786861104166257518854461558459:ℚ)/16574086654889062500000000000000000000000000000000000000000000),((29555747735048081893765303:ℚ)/115520000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((218755123:ℚ)/312500000),((442815119:ℚ)/625000000),((-5396596547:ℚ)/6734375000),((-1212530738:ℚ)/1691015625),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((1999830407:ℚ)/5000000000),((78959890695427219002253564232308237948167625981186374927187:ℚ)/2235769847811506688594818115234375000000000000000000000000000),((115495837090547718126853:ℚ)/451250000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((702986993:ℚ)/1000000000),((7114746983:ℚ)/10000000000),((-86731710779:ℚ)/108225000000),((-1948960979:ℚ)/2717500000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1949028863:ℚ)/5000000000),((2978674337018580500629056308536820831238269057307684792885781:ℚ)/84333264151077246093750000000000000000000000000000000000000000),((29578126837434581460135247:ℚ)/115520000000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((3529787881:ℚ)/5000000000),((714445191:ℚ)/1000000000),((-8711787483:ℚ)/10870000000),((-9789363643:ℚ)/13646875000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((3793877771:ℚ)/10000000000),((337973138168285785516268469810686783334039526108963344293723:ℚ)/9567865261734987109375000000000000000000000000000000000000000),((295893253632243813394463:ℚ)/1155200000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((3544640717:ℚ)/5000000000),((1434831337:ℚ)/2000000000),((-17500807381:ℚ)/21835000000),((-9833922151:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((3686902029:ℚ)/10000000000),((2763537772083903064936929300905731203849567970880069772945829:ℚ)/78227036518590602929687500000000000000000000000000000000000000),((1184021194898275334008687:ℚ)/4620800000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2193:ℚ)/3200),((8791:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((7118986949:ℚ)/10000000000),((7189009017:ℚ)/10000000000),((-29232372407:ℚ)/36550000000),((-19756960847:ℚ)/27471875000),((9662900309:ℚ)/10000000000),((9668970163:ℚ)/10000000000),((520776989:ℚ)/2000000000),((1788439581:ℚ)/5000000000),((826952162110610934132700079805959135207050484672256185112449143:ℚ)/23584068160277164843750000000000000000000000000000000000000000000),((29606134371401267371927247:ℚ)/115520000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((8791:ℚ)/12800) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8791:ℚ)/12800),((881:ℚ)/1280),((-13:ℚ)/16),((-3:ℚ)/4),((222932489:ℚ)/312500000),((112560333:ℚ)/156250000),((-2746568658:ℚ)/3433984375),((-1237594934:ℚ)/1720703125),((4828444327:ℚ)/5000000000),((4831450157:ℚ)/5000000000),((2627133759:ℚ)/10000000000),((110019873:ℚ)/312500000),((3444191510000656375146798746966098119861265605703693239421:ℚ)/98219288262944860570132732391357421875000000000000000000000),((14458857600854178821719:ℚ)/56406250000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((8791:ℚ)/12800) ((881:ℚ)/1280) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((881:ℚ)/1280),((8829:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((7148692309:ℚ)/10000000000),((7218713569:ℚ)/10000000000),((-88083276397:ℚ)/110125000000),((-19846076927:ℚ)/27590625000),((301591713:ℚ)/312500000),((9656888659:ℚ)/10000000000),((2649962557:ℚ)/10000000000),((865879571:ℚ)/2500000000),((7427770867894702406971761252969125703971670388478052599108599:ℚ)/211806656118514859676361083984375000000000000000000000000000000),((29617347857512267291395903:ℚ)/115520000000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((881:ℚ)/1280) ((8829:ℚ)/12800) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((8829:ℚ)/12800),((553:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((716354493:ℚ)/1000000000),((7233565791:ℚ)/10000000000),((-29425451761:ℚ)/36787500000),((-1989063479:ℚ)/2765000000),((1205629803:ℚ)/1250000000),((9650934821:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((68109643:ℚ)/200000000),((22347099926783644313624980591556131084020424081811029805029:ℚ)/637197914909596824645996093750000000000000000000000000000000),((82058052203355997430183:ℚ)/320000000000000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((8829:ℚ)/12800) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((553:ℚ)/800),((8867:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((3589198757:ℚ)/5000000000),((906052247:ℚ)/1250000000),((-11058679211:ℚ)/13825000000),((-9967596271:ℚ)/13854687500),((2409799777:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((673601917:ℚ)/2500000000),((3346479673:ℚ)/10000000000),((2846316403096072907789779427754933695172462695411217994422051:ℚ)/81153802095329302978515625000000000000000000000000000000000000),((462946364523137720045307:ℚ)/1805000000000000000000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((8867:ℚ)/12800) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((8867:ℚ)/12800),((4443:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((359662503:ℚ)/500000000),((1815817531:ℚ)/2500000000),((-22165627903:ℚ)/27709375000),((-998987509:ℚ)/1388437500),((4816708251:ℚ)/5000000000),((9639199113:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((657291749:ℚ)/2000000000),((2557476597632217055346884615051515034601638385540023522008927:ℚ)/72913900873777391576766967773437500000000000000000000000000000),((1852136206856804878669503:ℚ)/7220000000000000000000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((8867:ℚ)/12800) ((4443:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((901012821:ℚ)/1250000000),((1458594863:ℚ)/2000000000),((-17809733219:ℚ)/22215000000),((-2503038463:ℚ)/3485937500),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1612681221:ℚ)/5000000000),((753279963302009026259729081874179931301784742677811740840291:ℚ)/21315627786588663427734375000000000000000000000000000000000000),((1185816310434592799056287:ℚ)/4620800000000000000000000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7237807473:ℚ)/10000000000),((7322678363:ℚ)/10000000000),((-89434818719:ℚ)/111550000000),((-20113422419:ℚ)/28006250000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((77492199:ℚ)/250000000),((246258088552387652869971188681985287120694667034722897831231591:ℚ)/6967847232520067218750000000000000000000000000000000000000000000),((29656642198414397622989287:ℚ)/115520000000000000000000000)⟩
theorem valid16 : Valid source11 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-13:ℚ)/16),((-3:ℚ)/4),((726751223:ℚ)/1000000000),((114880973:ℚ)/156250000),((-1403452649:ℚ)/1750390625),((-2020253669:ℚ)/2812500000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((2968876971:ℚ)/10000000000),((3998367555931029631126402546390339822318636666665941:ℚ)/113125035972660407423973083496093750000000000000000000),((40128173995553315519:ℚ)/156250000000000000000)⟩
theorem valid17 : Valid source11 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source11 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7297216841:ℚ)/10000000000),((7382086043:ℚ)/10000000000),((-90207118559:ℚ)/112500000000),((-20291650523:ℚ)/28243750000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((70805431:ℚ)/250000000),((2141192050940609339518802480918313366272124198957581184148079837:ℚ)/60576058630371093750000000000000000000000000000000000000000000000),((29679129037268874614337127:ℚ)/115520000000000000000000000)⟩
theorem valid18 : Valid source11 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((1831730327:ℚ)/2500000000),((7411789677:ℚ)/10000000000),((-90593265801:ℚ)/112975000000),((-5095190981:ℚ)/7090625000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((1344408243:ℚ)/5000000000),((4100339786087741085666021358345544868152794557755280922078049:ℚ)/115994144936326073974609375000000000000000000000000000000000000),((29690381439162432837798167:ℚ)/115520000000000000000000000)⟩
theorem valid19 : Valid source11 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source11 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((229894551:ℚ)/312500000),((7471196543:ℚ)/10000000000),((-91365555059:ℚ)/113450000000),((-639683653:ℚ)/893750000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1268765727:ℚ)/5000000000),((6692222193663576592058696641383521346376512952279830073144571:ℚ)/186623183240578906250000000000000000000000000000000000000000000),((29712904211256593258856127:ℚ)/115520000000000000000000000)⟩
theorem valid20 : Valid source11 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((7416033863:ℚ)/10000000000),((7590008713:ℚ)/10000000000),((-92910113269:ℚ)/114400000000),((-20648101589:ℚ)/29075000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2204738609:ℚ)/10000000000),((42406807980251669457989309592118978821537534871012746732173919:ℚ)/1150601232809600000000000000000000000000000000000000000000000000),((29758021643870824944231087:ℚ)/115520000000000000000000000)⟩
theorem valid21 : Valid source11 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((7534848693:ℚ)/10000000000),((3854409441:ℚ)/5000000000),((-47227322733:ℚ)/58150000000),((-21004546079:ℚ)/29550000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((327582367:ℚ)/2500000000),((3952544996728322349302133385253799710712605846939393614039757:ℚ)/107310976037091210937500000000000000000000000000000000000000000),((16488543:ℚ)/64000000)⟩
theorem valid22 : Valid source11 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-13:ℚ)/16),((-3:ℚ)/4),((7653661437:ℚ)/10000000000),((1589286719:ℚ)/2000000000),((-19508727347:ℚ)/23640000000),((-21360984311:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((35676612641222553343118271668958198130770169147195449987809:ℚ)/921729227029200000000000000000000000000000000000000000000000),((16488543:ℚ)/64000000)⟩
theorem valid23 : Valid source11 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((3945640529:ℚ)/5000000000),((336865713:ℚ)/400000000),((-4148854269:ℚ)/4880000000),((-11036921587:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((201044713293344464885068236533285641706931290257264803069:ℚ)/4765511491200000000000000000000000000000000000000000000000),((16488543:ℚ)/64000000)⟩
theorem valid24 : Valid source11 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((8366499241:ℚ)/10000000000),((10322280883:ℚ)/10000000000),((-128429651479:ℚ)/129600000000),((-23499497723:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((157439066474096788389796229398545255485677224716641729477:ℚ)/2550916800000000000000000000000000000000000000000000000000),((16488543:ℚ)/64000000)⟩
theorem valid25 : Valid source11 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((2566791149:ℚ)/2500000000),((14123029753:ℚ)/10000000000),(-1:ℚ),((-7300373447:ℚ)/13800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1622276728027594503217891:ℚ)/23805000000000000000000000),((16488543:ℚ)/64000000)⟩
theorem valid26 : Valid source11 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet26 valid26
private theorem node1_3 :
    CellBound source11 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((4329:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source11 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4329:ℚ)/6400) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((4329:ℚ)/6400) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source11 nn0 nn1 Qcell ((4329:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source11 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source11 nn0 nn1 Qcell ((4329:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_6 node6_13
private theorem node14_16 :
    CellBound source11 nn0 nn1 Qcell ((8867:ℚ)/12800) ((2231:ℚ)/3200) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_join leaf13 node14_16
private theorem node16_18 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf16 leaf17
private theorem node18_20 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_join leaf18 leaf19
private theorem node16_20 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join node16_18 node18_20
private theorem node13_20 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join node13_16 node16_20
private theorem node21_23 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf20 node21_23
private theorem node23_25 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf23 leaf24
private theorem node25_27 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf25 leaf26
private theorem node23_27 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node23_25 node25_27
private theorem node20_27 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node20_23 node23_27
private theorem node13_27 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node13_20 node20_27
private theorem node0_27 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_13 node13_27
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_27
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26]
theorem packet_count : packets.length = 27 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC04
#check @N11Formalization.C450Source11GroupedC04.bound
#print axioms N11Formalization.C450Source11GroupedC04.valid0
#print axioms N11Formalization.C450Source11GroupedC04.valid1
#print axioms N11Formalization.C450Source11GroupedC04.valid2
#print axioms N11Formalization.C450Source11GroupedC04.valid3
#print axioms N11Formalization.C450Source11GroupedC04.valid4
#print axioms N11Formalization.C450Source11GroupedC04.valid5
#print axioms N11Formalization.C450Source11GroupedC04.valid6
#print axioms N11Formalization.C450Source11GroupedC04.valid7
#print axioms N11Formalization.C450Source11GroupedC04.valid8
#print axioms N11Formalization.C450Source11GroupedC04.valid9
#print axioms N11Formalization.C450Source11GroupedC04.valid10
#print axioms N11Formalization.C450Source11GroupedC04.valid11
#print axioms N11Formalization.C450Source11GroupedC04.valid12
#print axioms N11Formalization.C450Source11GroupedC04.valid13
#print axioms N11Formalization.C450Source11GroupedC04.valid14
#print axioms N11Formalization.C450Source11GroupedC04.valid15
#print axioms N11Formalization.C450Source11GroupedC04.valid16
#print axioms N11Formalization.C450Source11GroupedC04.valid17
#print axioms N11Formalization.C450Source11GroupedC04.valid18
#print axioms N11Formalization.C450Source11GroupedC04.valid19
#print axioms N11Formalization.C450Source11GroupedC04.valid20
#print axioms N11Formalization.C450Source11GroupedC04.valid21
#print axioms N11Formalization.C450Source11GroupedC04.valid22
#print axioms N11Formalization.C450Source11GroupedC04.valid23
#print axioms N11Formalization.C450Source11GroupedC04.valid24
#print axioms N11Formalization.C450Source11GroupedC04.valid25
#print axioms N11Formalization.C450Source11GroupedC04.valid26
#print axioms N11Formalization.C450Source11GroupedC04.bound
#print axioms N11Formalization.C450Source11GroupedC04.endpoint_checks
