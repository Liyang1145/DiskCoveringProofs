import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((3324943501:ℚ)/5000000000),((3420372171:ℚ)/5000000000),((-9429116513:ℚ)/9920000000),((-21034604507:ℚ)/25275000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((1263478053:ℚ)/2500000000),((16094468904094230080731285710233483431385563:ℚ)/259840057267200000000000000000000000000000000),((353838428517221796016065417:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((6768733169:ℚ)/10000000000),((1739887453:ℚ)/2500000000),((-4803662359:ℚ)/5055000000),((-42901132183:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((2360417279:ℚ)/5000000000),((1223735842088778244468098247320013408531179637080253523:ℚ)/19825958817236328125000000000000000000000000000000000000),((88749026687524640606886233:ℚ)/184832000000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((860946973:ℚ)/1250000000),((3509475893:ℚ)/5000000000),((-9696427679:ℚ)/10300000000),((-780946973:ℚ)/928125000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((872890881:ℚ)/2000000000),((15363546120808060585841992347558498522961111393060194641:ℚ)/261470149584960937500000000000000000000000000000000000000),((355575138357401484813855113:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((347349791:ℚ)/500000000),((7078353271:ℚ)/10000000000),((-19571059813:ℚ)/20790000000),((-2207448537:ℚ)/2622500000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((2087834023:ℚ)/5000000000),((1744882874345528673344526856374492364391221621629481695493:ℚ)/29726239491506250000000000000000000000000000000000000000000),((3946308016245582087491897:ℚ)/8192000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-15:ℚ)/16),((-7:ℚ)/8),((21895047:ℚ)/31250000),((3554026917:ℚ)/5000000000),((-9830080751:ℚ)/10490000000),((-278530658:ℚ)/329296875),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((397848447:ℚ)/1000000000),((293727401624081347987221429724975183087350884026648306470521:ℚ)/5126980093070006250000000000000000000000000000000000000000000),((356443926745353349368540393:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7036124351:ℚ)/10000000000),((178443857:ℚ)/250000000),((-493731571:ℚ)/526875000),((-44772870457:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((775268849:ℚ)/2000000000),((3128365480816751897674846822610270969810652363171530663:ℚ)/54623968111037658691406250000000000000000000000000000000),((891833967999717570248113:ℚ)/1848320000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((8487:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((1413166693:ℚ)/2000000000),((357630223:ℚ)/500000000),((-989690669:ℚ)/1058500000),((-8996166851:ℚ)/10608750000),((9767266893:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((2161672951:ℚ)/10000000000),((3771582993:ℚ)/10000000000),((839177660025622065352620798162040214145348998256143253899:ℚ)/14830592706078463476562500000000000000000000000000000000000),((3568784295013194896639473:ℚ)/7393280000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((2117:ℚ)/3200) ((8487:ℚ)/12800) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((8487:ℚ)/12800),((4253:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((141613759:ℚ)/200000000),((7167454611:ℚ)/10000000000),((-19838363833:ℚ)/21217500000),((-901696313:ℚ)/1063250000),((9760276751:ℚ)/10000000000),((4883633449:ℚ)/5000000000),((438804929:ℚ)/2000000000),((3718150311:ℚ)/10000000000),((565676739404559319138623397898632351558552761650724737930741:ℚ)/9998380488914821801757812500000000000000000000000000000000000),((1428093119395519660850704377:ℚ)/2957312000000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((8487:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4253:ℚ)/6400),((341:ℚ)/512),((-15:ℚ)/16),((-7:ℚ)/8),((7095542387:ℚ)/10000000000),((7182304733:ℚ)/10000000000),((-19882914199:ℚ)/21265000000),((-45188796709:ℚ)/53281250000),((195067017:ℚ)/200000000),((2440069189:ℚ)/2500000000),((1112811311:ℚ)/5000000000),((18319877:ℚ)/50000000),((24708549133917603386086645164469848871224417932391479687921:ℚ)/436782222513273291015625000000000000000000000000000000000000),((1428672552970078036942767193:ℚ)/2957312000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((4253:ℚ)/6400) ((341:ℚ)/512) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((341:ℚ)/512),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((888799597:ℚ)/1250000000),((7197154827:ℚ)/10000000000),((-19927464481:ℚ)/21312500000),((-5661597179:ℚ)/6675000000),((4873244381:ℚ)/5000000000),((1950670171:ℚ)/2000000000),((2256500263:ℚ)/10000000000),((1804512387:ℚ)/5000000000),((887154634835556356721479753443210231822428513719071367701:ℚ)/15684585112243652343750000000000000000000000000000000000000),((1429252018767780045842436873:ℚ)/2957312000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((341:ℚ)/512) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((267:ℚ)/400),((8563:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7125251117:ℚ)/10000000000),((7212004893:ℚ)/10000000000),((-19972014679:ℚ)/21360000000),((-45396757819:ℚ)/53518750000),((9739690061:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((1143344217:ℚ)/5000000000),((3553262383:ℚ)/10000000000),((84194757618134043001167649123632519731602646079953190372893507:ℚ)/1488724706043676800000000000000000000000000000000000000000000000),((1429831516788437236649233113:ℚ)/2957312000000000000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((8563:ℚ)/12800) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8563:ℚ)/12800),((4291:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((1785026353:ℚ)/2500000000),((722685493:ℚ)/1000000000),((-2001656479:ℚ)/2140750000),((-1625026353:ℚ)/1915625000),((1216619291:ℚ)/1250000000),((4869845033:ℚ)/5000000000),((1158107867:ℚ)/5000000000),((1748324661:ℚ)/5000000000),((325727340179804076295537278100228467297290644628913433521:ℚ)/5760216848505044995117187500000000000000000000000000000000),((14304110469928345313362313:ℚ)/29573120000000000000000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((8563:ℚ)/12800) ((4291:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4291:ℚ)/6400),((8601:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((357747983:ℚ)/500000000),((362085247:ℚ)/500000000),((-1003055741:ℚ)/1072750000),((-760078627:ℚ)/895937500),((1215785143:ℚ)/1250000000),((9732954333:ℚ)/10000000000),((2345108749:ℚ)/10000000000),((3439143521:ℚ)/10000000000),((76294560390513388834516616479146387233304895408496821837:ℚ)/1349376414445671582031250000000000000000000000000000000000),((3577476523647086228066833:ℚ)/7393280000000000000000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((4291:ℚ)/6400) ((8601:ℚ)/12800) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((8601:ℚ)/12800),((431:ℚ)/640),((-15:ℚ)/16),((-7:ℚ)/8),((7169813861:ℚ)/10000000000),((3628277461:ℚ)/5000000000),((-10052832383:ℚ)/10751250000),((-45708697027:ℚ)/53875000000),((607479381:ℚ)/625000000),((9726281149:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3380699361:ℚ)/10000000000),((9063059295508364186382490535929561197808351934109217259017:ℚ)/160313069742159777832031250000000000000000000000000000000000),((357892551036806070614776777:ℚ)/739328000000000000000000000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell ((8601:ℚ)/12800) ((431:ℚ)/640) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((431:ℚ)/640),((8639:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((449041751:ℚ)/625000000),((7271404877:ℚ)/10000000000),((-20150214631:ℚ)/21550000000),((-2863292257:ℚ)/3374609375),((4856560387:ℚ)/5000000000),((9719670101:ℚ)/10000000000),((9604357:ℚ)/40000000),((830316809:ℚ)/2500000000),((1618873272929481708294550814475924525292206491013090592752963:ℚ)/28639219922028906250000000000000000000000000000000000000000000),((1432149831096848813374489273:ℚ)/2957312000000000000000000000)⟩
theorem valid14 : Valid source15 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source15 nn0 nn1 Qcell ((431:ℚ)/640) ((8639:ℚ)/12800) :=
  cell_of_packet source15 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((8639:ℚ)/12800),((4329:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((3599761063:ℚ)/5000000000),((1457250961:ℚ)/2000000000),((-4038952883:ℚ)/4319500000),((-22958327441:ℚ)/27056250000),((2426658193:ℚ)/2500000000),((9713120779:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((1630396527:ℚ)/5000000000),((533523326009156892037923848371847427761906973166308569710213:ℚ)/9439644175146679436718750000000000000000000000000000000000000),((158751190061775774533257:ℚ)/327680000000000000000000)⟩
theorem valid15 : Valid source15 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source15 nn0 nn1 Qcell ((8639:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((4329:ℚ)/6400),((8677:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7214376189:ℚ)/10000000000),((3650552353:ℚ)/5000000000),((-10119657059:ℚ)/10822500000),((-46020633323:ℚ)/54231250000),((9700205687:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((306851119:ℚ)/1250000000),((1599608833:ℚ)/5000000000),((11236342939392208648604189556384351627425088763856324635509127:ℚ)/198829463647408596386718750000000000000000000000000000000000000),((358327295444768804835934033:ℚ)/739328000000000000000000000)⟩
theorem valid16 : Valid source15 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source15 nn0 nn1 Qcell ((4329:ℚ)/6400) ((8677:ℚ)/12800) :=
  cell_of_packet source15 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((8677:ℚ)/12800),((1087:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((56478361:ℚ)/78125000),((7315954579:ℚ)/10000000000),((-20283863737:ℚ)/21692500000),((-360348527:ℚ)/424609375),((9693839119:ℚ)/10000000000),((2425051423:ℚ)/2500000000),((2480870833:ℚ)/10000000000),((3136476133:ℚ)/10000000000),((266218955601879389384891971138968992315998907368316248715887:ℚ)/4711377908696204083251953125000000000000000000000000000000000),((3971991427901034818964497:ℚ)/8192000000000000000000000)⟩
theorem valid17 : Valid source15 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source15 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1087:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1087:ℚ)/1600),((1743:ℚ)/2560),((-15:ℚ)/16),((-7:ℚ)/8),((3622042091:ℚ)/5000000000),((3665402213:ℚ)/5000000000),((-10164206639:ℚ)/10870000000),((-1100680697:ℚ)/1296875000),((9687532673:ℚ)/10000000000),((2423459781:ℚ)/2500000000),((2506424897:ℚ)/10000000000),((384062119:ℚ)/1250000000),((195273362241477052109366202240204642447960192218487075929:ℚ)/3456247636783984375000000000000000000000000000000000000000),((358617165366254407767362153:ℚ)/739328000000000000000000000)⟩
theorem valid18 : Valid source15 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1743:ℚ)/2560) :=
  cell_of_packet source15 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((1743:ℚ)/2560),((4367:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7258938111:ℚ)/10000000000),((7345654247:ℚ)/10000000000),((-20372962741:ℚ)/21787500000),((-46332566777:ℚ)/54587500000),((2420321489:ℚ)/2500000000),((4843766339:ℚ)/5000000000),((2531487941:ℚ)/10000000000),((150360053:ℚ)/500000000),((276346301139696961832803729417139224065303851095401416804317:ℚ)/4891792881874758911132812500000000000000000000000000000000000),((1435048449757132416402248833:ℚ)/2957312000000000000000000000)⟩
theorem valid19 : Valid source15 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source15 nn0 nn1 Qcell ((1743:ℚ)/2560) ((4367:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((1818447999:ℚ)/2500000000),((460959613:ℚ)/625000000),((-1278878839:ℚ)/1364687500),((-11609135993:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((367562583:ℚ)/1250000000),((396714632788641027912937194502320034775773492702923493039:ℚ)/6944871850016921424865722656250000000000000000000000000000),((5610187980943855570620953:ℚ)/11552000000000000000000000)⟩
theorem valid20 : Valid source15 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source15 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-15:ℚ)/16),((-7:ℚ)/8),((3651749817:ℚ)/5000000000),((3702526633:ℚ)/5000000000),((-10275579899:ℚ)/10965000000),((-23322248719:ℚ)/27531250000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((560496569:ℚ)/2000000000),((314562806011300421139385402080595970627894285421532175749:ℚ)/5508400670357031250000000000000000000000000000000000000000),((359341981430132830059736993:ℚ)/739328000000000000000000000)⟩
theorem valid21 : Valid source15 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source15 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((7333207097:ℚ)/10000000000),((7434752621:ℚ)/10000000000),((-20640257863:ℚ)/22025000000),((-6693207097:ℚ)/7900000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2657504833:ℚ)/10000000000),((23792127634954768179127652443976119486810290722199407976473:ℚ)/416756086492285156250000000000000000000000000000000000000000),((1438527857552458872763572217:ℚ)/2957312000000000000000000000)⟩
theorem valid22 : Valid source15 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source15 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((736291439:ℚ)/1000000000),((1873537757:ℚ)/2500000000),((-5204613271:ℚ)/5530000000),((-4706040073:ℚ)/5577500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((7826117:ℚ)/31250000),((43832567076955835649718804849526810398076956823879969594367:ℚ)/751547633836693750000000000000000000000000000000000000000000),((90053006821515007894068313:ℚ)/184832000000000000000000000)⟩
theorem valid23 : Valid source15 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-15:ℚ)/16),((-7:ℚ)/8),((1855582117:ℚ)/2500000000),((7553549039:ℚ)/10000000000),((-20996647117:ℚ)/22310000000),((-1318786091:ℚ)/1562500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1083270339:ℚ)/5000000000),((175846099592133990881574130691198473373976137576678821:ℚ)/3017525106250000000000000000000000000000000000000000000),((1443168878276800821455305777:ℚ)/2957312000000000000000000000)⟩
theorem valid24 : Valid source15 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source15 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((3740870943:ℚ)/5000000000),((1534468783:ℚ)/2000000000),((-4270606349:ℚ)/4500000000),((-23946096601:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((70655899:ℚ)/400000000),((78500479257973952139038366421984226070639700493803067091:ℚ)/1294038281250000000000000000000000000000000000000000000000),((20013631:ℚ)/40960000)⟩
theorem valid25 : Valid source15 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((1520113361:ℚ)/2000000000),((8622655527:ℚ)/10000000000),(-1:ℚ),((-3248264509:ℚ)/4320000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((7606349883491968193330908968102791:ℚ)/93312000000000000000000000000000000),((20013631:ℚ)/40960000)⟩
theorem valid26 : Valid source15 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((1710217403:ℚ)/2000000000),((657693817:ℚ)/625000000),(-1:ℚ),((-11075521821:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((28050616368932941124115705894251299:ℚ)/320000000000000000000000000000000000),((20013631:ℚ)/40960000)⟩
theorem valid27 : Valid source15 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((2090366149:ℚ)/2000000000),((3580906007:ℚ)/2500000000),(-1:ℚ),((-13736563043:ℚ)/22080000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((23995296053862043715362241:ℚ)/243763200000000000000000000),((20013631:ℚ)/40960000)⟩
theorem valid28 : Valid source15 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet28 valid28
private theorem node1_3 :
    CellBound source15 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2079:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source15 nn0 nn1 Qcell ((2079:ℚ)/3200) ((843:ℚ)/1280) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source15 nn0 nn1 Qcell ((843:ℚ)/1280) ((8487:ℚ)/12800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source15 nn0 nn1 Qcell ((2079:ℚ)/3200) ((8487:ℚ)/12800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((8487:ℚ)/12800) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source15 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source15 nn0 nn1 Qcell ((8487:ℚ)/12800) ((267:ℚ)/400) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source15 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source15 nn0 nn1 Qcell ((8487:ℚ)/12800) ((431:ℚ)/640) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_7 node7_14
private theorem node15_17 :
    CellBound source15 nn0 nn1 Qcell ((8639:ℚ)/12800) ((8677:ℚ)/12800) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source15 nn0 nn1 Qcell ((431:ℚ)/640) ((8677:ℚ)/12800) :=
  cell_join leaf14 node15_17
private theorem node17_19 :
    CellBound source15 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1743:ℚ)/2560) :=
  cell_join leaf17 leaf18
private theorem node19_21 :
    CellBound source15 nn0 nn1 Qcell ((1743:ℚ)/2560) ((2193:ℚ)/3200) :=
  cell_join leaf19 leaf20
private theorem node17_21 :
    CellBound source15 nn0 nn1 Qcell ((8677:ℚ)/12800) ((2193:ℚ)/3200) :=
  cell_join node17_19 node19_21
private theorem node14_21 :
    CellBound source15 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join node14_17 node17_21
private theorem node21_23 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf21 leaf22
private theorem node23_25 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf23 leaf24
private theorem node21_25 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join node21_23 node23_25
private theorem node25_27 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((81:ℚ)/100) :=
  cell_join leaf25 leaf26
private theorem node27_29 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf27 leaf28
private theorem node25_29 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node25_27 node27_29
private theorem node21_29 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node21_25 node25_29
private theorem node14_29 :
    CellBound source15 nn0 nn1 Qcell ((431:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node14_21 node21_29
private theorem node0_29 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_14 node14_29
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_29
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28]
theorem packet_count : packets.length = 29 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC02
#check @N11Formalization.C450Source15GroupedC02.bound
#print axioms N11Formalization.C450Source15GroupedC02.valid0
#print axioms N11Formalization.C450Source15GroupedC02.valid1
#print axioms N11Formalization.C450Source15GroupedC02.valid2
#print axioms N11Formalization.C450Source15GroupedC02.valid3
#print axioms N11Formalization.C450Source15GroupedC02.valid4
#print axioms N11Formalization.C450Source15GroupedC02.valid5
#print axioms N11Formalization.C450Source15GroupedC02.valid6
#print axioms N11Formalization.C450Source15GroupedC02.valid7
#print axioms N11Formalization.C450Source15GroupedC02.valid8
#print axioms N11Formalization.C450Source15GroupedC02.valid9
#print axioms N11Formalization.C450Source15GroupedC02.valid10
#print axioms N11Formalization.C450Source15GroupedC02.valid11
#print axioms N11Formalization.C450Source15GroupedC02.valid12
#print axioms N11Formalization.C450Source15GroupedC02.valid13
#print axioms N11Formalization.C450Source15GroupedC02.valid14
#print axioms N11Formalization.C450Source15GroupedC02.valid15
#print axioms N11Formalization.C450Source15GroupedC02.valid16
#print axioms N11Formalization.C450Source15GroupedC02.valid17
#print axioms N11Formalization.C450Source15GroupedC02.valid18
#print axioms N11Formalization.C450Source15GroupedC02.valid19
#print axioms N11Formalization.C450Source15GroupedC02.valid20
#print axioms N11Formalization.C450Source15GroupedC02.valid21
#print axioms N11Formalization.C450Source15GroupedC02.valid22
#print axioms N11Formalization.C450Source15GroupedC02.valid23
#print axioms N11Formalization.C450Source15GroupedC02.valid24
#print axioms N11Formalization.C450Source15GroupedC02.valid25
#print axioms N11Formalization.C450Source15GroupedC02.valid26
#print axioms N11Formalization.C450Source15GroupedC02.valid27
#print axioms N11Formalization.C450Source15GroupedC02.valid28
#print axioms N11Formalization.C450Source15GroupedC02.bound
#print axioms N11Formalization.C450Source15GroupedC02.endpoint_checks
