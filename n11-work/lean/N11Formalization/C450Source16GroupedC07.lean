import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((40610547:ℚ)/62500000),((3397719279:ℚ)/5000000000),((-2949719279:ℚ)/4960000000),((-305494923:ℚ)/643750000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5453247603:ℚ)/10000000000),((18146207770088731161146477159807192243019727466889759851:ℚ)/303410610240000000000000000000000000000000000000000000000),((568935090941785997039:ℚ)/2280000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((6735827923:ℚ)/10000000000),((6914498383:ℚ)/10000000000),((-6018498383:ℚ)/10300000000),((-51022451307:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4815175091:ℚ)/10000000000),((1351439863733354440946339334792848097100891238533242038481:ℚ)/23485114912636718750000000000000000000000000000000000000000),((4829812467921716517546053:ℚ)/19456000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((6854880659:ℚ)/10000000000),((1743506027:ℚ)/2500000000),((-1519506027:ℚ)/2622500000),((-52093925931:ℚ)/105850000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1116284633:ℚ)/2500000000),((4885906377829817634611127902173110816464799763421407973:ℚ)/86507821782296142578125000000000000000000000000000000000),((4817191451482619255070917:ℚ)/19456000000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((864300367:ℚ)/1250000000),((7033547141:ℚ)/10000000000),((-6137547141:ℚ)/10585000000),((-2192901101:ℚ)/4450000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((856037647:ℚ)/2000000000),((142032291141354953744168831827243601941484840384428659:ℚ)/2513389400637207031250000000000000000000000000000000000),((3956301977453844725967:ℚ)/16000000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/8),((-9:ℚ)/16),((6973922583:ℚ)/10000000000),((1418613511:ℚ)/2000000000),((-413137837:ℚ)/712000000),((-53165303247:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4087423903:ℚ)/10000000000),((3470706798692705194691460529016925609071684752755673:ℚ)/61385506129218750000000000000000000000000000000000000),((758608914274963424052701:ℚ)/3072000000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((7033439671:ℚ)/10000000000),((7122826801:ℚ)/10000000000),((-6226826801:ℚ)/10775000000),((-17900319013:ℚ)/36075000000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((3885678759:ℚ)/10000000000),((712679834099271988536794370168298165879354164446163031207:ℚ)/12719046245327682495117187500000000000000000000000000000000),((4798171202976400632970637:ℚ)/19456000000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((1765799319:ℚ)/2500000000),((3576292709:ℚ)/5000000000),((-3128292709:ℚ)/5411250000),((-13492193871:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3780990391:ℚ)/10000000000),((568124901117352634906474543665288497233691399159513089:ℚ)/10136209633542938232421875000000000000000000000000000000),((899060775169829449769831:ℚ)/3648000000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((3546477133:ℚ)/5000000000),((3591171707:ℚ)/5000000000),((-3143171707:ℚ)/5435000000),((-27118294197:ℚ)/54587500000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((1836734627:ℚ)/5000000000),((838162767553476661510781717986216644567091499985789701469:ℚ)/14949789471460917358398437500000000000000000000000000000000),((1197951859196789215498373:ℚ)/4864000000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7122710649:ℚ)/10000000000),((1803025199:ℚ)/2500000000),((-1579025199:ℚ)/2729375000),((-18168131947:ℚ)/36550000000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((1781429181:ℚ)/5000000000),((23801237619046374078210065146223906308616902497872760461:ℚ)/424408835278811864852905273437500000000000000000000000000),((756098069992306812202109:ℚ)/3072000000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-5:ℚ)/8),((-9:ℚ)/16),((3576233217:ℚ)/5000000000),((3620928787:ℚ)/5000000000),((-1057642929:ℚ)/1827500000),((-27386098953:ℚ)/55062500000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((3448859897:ℚ)/10000000000),((305308500861902943276123628779070806494632786591900111:ℚ)/5442583382935485839843750000000000000000000000000000000),((3589073864713724686742519:ℚ)/14592000000000000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((7182221627:ℚ)/10000000000),((1454322751:ℚ)/2000000000),((-1275122751:ℚ)/2202500000),((-55039994643:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((832781383:ℚ)/2500000000),((1790389187148227369338839548425834522827793093892232511:ℚ)/31907887872065582275390625000000000000000000000000000000),((4782239565326747754118453:ℚ)/19456000000000000000000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((7211976237:ℚ)/10000000000),((3650684673:ℚ)/5000000000),((-3202684673:ℚ)/5530000000),((-18435928711:ℚ)/37025000000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3209243543:ℚ)/10000000000),((1219828381620415492697909841592308503397572522803962245477:ℚ)/21733856972408027343750000000000000000000000000000000000000),((14337133038871162403413199:ℚ)/58368000000000000000000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7241730271:ℚ)/10000000000),((1832781089:ℚ)/2500000000),((-536260363:ℚ)/925625000),((-55575572439:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1541360709:ℚ)/5000000000),((8656371400817119444773550576142060614584185523686256823:ℚ)/154192909335855493545532226562500000000000000000000000000),((4775846161934395581727037:ℚ)/19456000000000000000000000)⟩
theorem valid12 : Valid source16 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source16 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/8),((-9:ℚ)/16),((7271483737:ℚ)/10000000000),((3695316329:ℚ)/5000000000),((-3247316329:ℚ)/5577500000),((-18614451211:ℚ)/37500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((590192351:ℚ)/2000000000),((216023603735056810175052199147497672104853038768371:ℚ)/3812424908409118652343750000000000000000000000000000),((4772645011573456805522733:ℚ)/19456000000000000000000000)⟩
theorem valid13 : Valid source16 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source16 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source16 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7330988991:ℚ)/10000000000),((7450138721:ℚ)/10000000000),((-2184712907:ℚ)/3750000000),((-56378900919:ℚ)/113450000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((2668594917:ℚ)/10000000000),((3005729628376055034068762831576904092456776914157306189:ℚ)/53026484298706054687500000000000000000000000000000000000),((752563233272564829318029:ℚ)/3072000000000000000000000)⟩
theorem valid14 : Valid source16 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((7390492057:ℚ)/10000000000),((37548213:ℚ)/50000000),((-33068213:ℚ)/56725000),((-56914428513:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2353483763:ℚ)/10000000000),((2116410378762956217144074737372840332854321902865193:ℚ)/37324636648115781250000000000000000000000000000000000),((4759810738852994770661293:ℚ)/19456000000000000000000000)⟩
theorem valid15 : Valid source16 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source16 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((744999299:ℚ)/1000000000),((968454667:ℚ)/1250000000),((-856454667:ℚ)/1430000000),((-1914997897:ℚ)/3940000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1990127551:ℚ)/10000000000),((10167155843238777966638747911395907831705631058606633:ℚ)/170501125996093750000000000000000000000000000000000000),((47533757913354536534757:ℚ)/194560000000000000000000)⟩
theorem valid16 : Valid source16 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/8),((-9:ℚ)/16),((1537595283:ℚ)/2000000000),((7985601161:ℚ)/10000000000),((-2363200387:ℚ)/3940000000),((-11918357547:ℚ)/24400000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((3177300592439112395116458735949335100737824695528534423:ℚ)/53340811749375000000000000000000000000000000000000000000),((249321:ℚ)/1024000)⟩
theorem valid17 : Valid source16 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((3962964819:ℚ)/5000000000),((8461446997:ℚ)/10000000000),((-7565446997:ℚ)/12200000000),((-10288894457:ℚ)/21600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((6512757411909471463215946864245101519316988949186658379:ℚ)/103418218125000000000000000000000000000000000000000000000),((249321:ℚ)/1024000)⟩
theorem valid18 : Valid source16 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((4200878073:ℚ)/5000000000),((1036402523:ℚ)/1000000000),((-315600841:ℚ)/432000000),((-33007902657:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1535140151618449181968798115851621975600359624061:ℚ)/18895680000000000000000000000000000000000000000000),((249321:ℚ)/1024000)⟩
theorem valid19 : Valid source16 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((10304275497:ℚ)/10000000000),((14167049343:ℚ)/10000000000),((-13271049343:ℚ)/16000000000),((-27712826491:ℚ)/73600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((12745974936874277600490172667207853097404445430740167763:ℚ)/126960000000000000000000000000000000000000000000000000000),((249321:ℚ)/1024000)⟩
theorem valid20 : Valid source16 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source16 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source16 nn0 nn1 Qcell ((1049:ℚ)/1600) ((431:ℚ)/640) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source16 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source16 nn0 nn1 Qcell ((4367:ℚ)/6400) ((881:ℚ)/1280) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source16 nn0 nn1 Qcell ((1087:ℚ)/1600) ((881:ℚ)/1280) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source16 nn0 nn1 Qcell ((431:ℚ)/640) ((881:ℚ)/1280) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((881:ℚ)/1280) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source16 nn0 nn1 Qcell ((881:ℚ)/1280) ((4443:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source16 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source16 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source16 nn0 nn1 Qcell ((881:ℚ)/1280) ((2269:ℚ)/3200) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source16 nn0 nn1 Qcell ((2269:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound source16 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound source16 nn0 nn1 Qcell ((881:ℚ)/1280) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC07
#check @N11Formalization.C450Source16GroupedC07.bound
#print axioms N11Formalization.C450Source16GroupedC07.valid0
#print axioms N11Formalization.C450Source16GroupedC07.valid1
#print axioms N11Formalization.C450Source16GroupedC07.valid2
#print axioms N11Formalization.C450Source16GroupedC07.valid3
#print axioms N11Formalization.C450Source16GroupedC07.valid4
#print axioms N11Formalization.C450Source16GroupedC07.valid5
#print axioms N11Formalization.C450Source16GroupedC07.valid6
#print axioms N11Formalization.C450Source16GroupedC07.valid7
#print axioms N11Formalization.C450Source16GroupedC07.valid8
#print axioms N11Formalization.C450Source16GroupedC07.valid9
#print axioms N11Formalization.C450Source16GroupedC07.valid10
#print axioms N11Formalization.C450Source16GroupedC07.valid11
#print axioms N11Formalization.C450Source16GroupedC07.valid12
#print axioms N11Formalization.C450Source16GroupedC07.valid13
#print axioms N11Formalization.C450Source16GroupedC07.valid14
#print axioms N11Formalization.C450Source16GroupedC07.valid15
#print axioms N11Formalization.C450Source16GroupedC07.valid16
#print axioms N11Formalization.C450Source16GroupedC07.valid17
#print axioms N11Formalization.C450Source16GroupedC07.valid18
#print axioms N11Formalization.C450Source16GroupedC07.valid19
#print axioms N11Formalization.C450Source16GroupedC07.valid20
#print axioms N11Formalization.C450Source16GroupedC07.bound
#print axioms N11Formalization.C450Source16GroupedC07.endpoint_checks
