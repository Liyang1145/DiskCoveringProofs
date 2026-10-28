import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((6393421167:ℚ)/10000000000),((334053633:ℚ)/500000000),((-2242375431:ℚ)/2480000000),((-78634475171:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2856121923:ℚ)/5000000000),((58525123314321244007164305007795885058373:ℚ)/3160527190000000000000000000000000000000000),((21712617258047379584474759:ℚ)/110899200000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((663097943:ℚ)/1000000000),((3399924259:ℚ)/5000000000),((-22839469813:ℚ)/25750000000),((-8172273259:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2552530869:ℚ)/5000000000),((7858767135850490179758042895966338918782640854165049788859:ℚ)/458693650637435913085937500000000000000000000000000000000000),((724783845840316780629726037:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((6749756977:ℚ)/10000000000),((216206983:ℚ)/312500000),((-1453448881:ℚ)/1639062500),((-27755613567:ℚ)/35600000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((477544997:ℚ)/1000000000),((238687180491291225833206797970013919143037759513185952383:ℚ)/13951681306044006347656250000000000000000000000000000000000),((2835215740866430002935453:ℚ)/14440000000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-7:ℚ)/8),((-13:ℚ)/16),((858566693:ℚ)/1250000000),((1395602119:ℚ)/2000000000),((-9385214833:ℚ)/10680000000),((-10601367009:ℚ)/13468750000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4423355033:ℚ)/10000000000),((69920609950038516894603535433183091746541263065976887949813:ℚ)/4242966183651600000000000000000000000000000000000000000000000),((116213034265753059229863197:ℚ)/591462400000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((1731980369:ℚ)/2500000000),((3518698761:ℚ)/5000000000),((-23670891327:ℚ)/26937500000),((-21395744797:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2118565243:ℚ)/5000000000),((2378128437780124174082839844297585836682080513988759632055329:ℚ)/144348065510374450683593750000000000000000000000000000000000000),((2180544181349813401416839351:ℚ)/11089920000000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((3493654591:ℚ)/5000000000),((1766772727:ℚ)/2500000000),((-11887409089:ℚ)/13587500000),((-3925228153:ℚ)/4962500000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((4042877929:ℚ)/10000000000),((7493719691656943519590946974713518210917616532102220467461:ℚ)/463319921636185455322265625000000000000000000000000000000000),((181776623570451951008783933:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((877125369:ℚ)/1250000000),((3548392121:ℚ)/5000000000),((-23878744847:ℚ)/27293750000),((-10842629797:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((3942371101:ℚ)/10000000000),((898590044814110990132941957029080963448807254017296579469019:ℚ)/55558974800135371398925781250000000000000000000000000000000000),((727365018568395362249520157:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-7:ℚ)/8),((-13:ℚ)/16),((1761674167:ℚ)/2500000000),((3563238763:ℚ)/5000000000),((-1410745373:ℚ)/1612500000),((-21781764171:ℚ)/27531250000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((3839375297:ℚ)/10000000000),((7649979747005758444242693139430607986880550593590475617:ℚ)/473001533239746093750000000000000000000000000000000000000),((727623633326645011181806213:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((707639033:ℚ)/1000000000),((7156170761:ℚ)/10000000000),((-48173195327:ℚ)/55062500000),((-8751307429:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3733684073:ℚ)/10000000000),((737203789219860124608831152397705562374085327625283044573527:ℚ)/45582696960093688964843750000000000000000000000000000000000000),((2911529354259246602246381117:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7106083939:ℚ)/10000000000),((3592931973:ℚ)/5000000000),((-24190523811:ℚ)/27650000000),((-29299697069:ℚ)/37025000000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((906265297:ℚ)/2500000000),((669505724411528948798706129651925312563262626726791186199891:ℚ)/41397822804586718750000000000000000000000000000000000000000000),((2184423402821184135526013999:ℚ)/11089920000000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4443:ℚ)/6400),((1781:ℚ)/2560),((-7:ℚ)/8),((-13:ℚ)/16),((891972187:ℚ)/1250000000),((7200710521:ℚ)/10000000000),((-48484973647:ℚ)/55537500000),((-11035638431:ℚ)/13914062500),((9627690243:ℚ)/10000000000),((9633416507:ℚ)/10000000000),((2737309683:ℚ)/10000000000),((351323423:ℚ)/1000000000),((4186891952724525239235857066390373834797558848405358231152813:ℚ)/261230260023548327636718750000000000000000000000000000000000000),((2913082264261889175802745757:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((4443:ℚ)/6400) ((1781:ℚ)/2560) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1781:ℚ)/2560),((2231:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((1430124851:ℚ)/2000000000),((7215557083:ℚ)/10000000000),((-48588899581:ℚ)/55656250000),((-17695623063:ℚ)/22310000000),((2405504993:ℚ)/2500000000),((1203461281:ℚ)/1250000000),((551641531:ℚ)/2000000000),((1728011111:ℚ)/5000000000),((1343119288833957215567591489301103739064442382141437394659497:ℚ)/83799418957037630677223205566406250000000000000000000000000000),((2913600081881501886943423653:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((1781:ℚ)/2560) ((2231:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2231:ℚ)/3200),((8943:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7165471001:ℚ)/10000000000),((3615201817:ℚ)/5000000000),((-24346412719:ℚ)/27887500000),((-8061011183:ℚ)/10162500000),((961640533:ℚ)/1000000000),((9622019977:ℚ)/10000000000),((555749933:ℚ)/2000000000),((84947159:ℚ)/250000000),((62436808407096040088300849027973661934413554655782317467991:ℚ)/3895489359283117675781250000000000000000000000000000000000000),((728529497505821445341413853:ℚ)/3696640000000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((8943:ℚ)/12800) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((8943:ℚ)/12800),((4481:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((1436063547:ℚ)/2000000000),((1811312543:ℚ)/2500000000),((-12199187801:ℚ)/13973437500),((-17772826111:ℚ)/22405000000),((1922169193:ℚ)/2000000000),((1923281067:ℚ)/2000000000),((349868089:ℚ)/1250000000),((3338778317:ℚ)/10000000000),((658573838075690064987746578735719202900972501583369269027999:ℚ)/41088560036707595807075500488281250000000000000000000000000000),((182164749288578267990574573:ℚ)/924160000000000000000000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((8943:ℚ)/12800) ((4481:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4481:ℚ)/6400),((8981:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((899395557:ℚ)/1250000000),((7260096699:ℚ)/10000000000),((-48900676893:ℚ)/56012500000),((-11132142241:ℚ)/14032812500),((4802670763:ℚ)/5000000000),((961084597:ℚ)/1000000000),((563760281:ℚ)/2000000000),((819661363:ℚ)/2500000000),((14199481989363258668174892853498400866804554361783788548622211:ℚ)/885899141629319506958007812500000000000000000000000000000000000),((8745462233198884098268973231:ℚ)/44359680000000000000000000000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((4481:ℚ)/6400) ((8981:ℚ)/12800) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((8981:ℚ)/12800),((45:ℚ)/64),((-7:ℚ)/8),((-13:ℚ)/16),((1802502791:ℚ)/2500000000),((3637471607:ℚ)/5000000000),((-24502301249:ℚ)/28065625000),((-22312536283:ℚ)/28125000000),((599993229:ℚ)/625000000),((9605341531:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1608715119:ℚ)/5000000000),((8542059092551717089558395696219779439603785665294832483:ℚ)/532929665260505676269531250000000000000000000000000000000),((728918064333826363718995773:ℚ)/3696640000000000000000000000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell ((8981:ℚ)/12800) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((361242893:ℚ)/500000000),((730463621:ℚ)/1000000000),((-4921245347:ℚ)/5625000000),((-4472157609:ℚ)/5648750000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((631013921:ℚ)/2000000000),((367333514947734852585784133604898440392586736427058405019541:ℚ)/22716021986389160156250000000000000000000000000000000000000000),((29167088880688524463501157:ℚ)/147865600000000000000000000)⟩
theorem valid16 : Valid eighth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((3627275607:ℚ)/5000000000),((7334329159:ℚ)/10000000000),((-49420304113:ℚ)/56487500000),((-44914582891:ℚ)/56725000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((3026627317:ℚ)/10000000000),((23445572668201345653617337096423364443721322168102365385690559:ℚ)/1449926811704075924682617187500000000000000000000000000000000000),((2917745880781273319831697437:ℚ)/14786560000000000000000000000)⟩
theorem valid17 : Valid eighth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound eighth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7284244519:ℚ)/10000000000),((7364022063:ℚ)/10000000000),((-49628154441:ℚ)/56725000000),((-30071726249:ℚ)/37975000000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((1446334911:ℚ)/5000000000),((1702471197995383866163571548084211179989710869800530593630567:ℚ)/105288047020677144531250000000000000000000000000000000000000000),((8756349706622177612088478439:ℚ)/44359680000000000000000000000)⟩
theorem valid18 : Valid eighth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((457121111:ℚ)/625000000),((3696857461:ℚ)/5000000000),((-24918002227:ℚ)/28481250000),((-5662574443:ℚ)/7150000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((1376195677:ℚ)/5000000000),((131163784285843809764974888753972236605912524405253929519:ℚ)/8111998214617538452148437500000000000000000000000000000000),((729955238086389223340750917:ℚ)/3696640000000000000000000000)⟩
theorem valid19 : Valid eighth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound eighth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((1468726197:ℚ)/2000000000),((1863275127:ℚ)/2500000000),((-12562925889:ℚ)/14300000000),((-18197440561:ℚ)/23070000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((325596279:ℚ)/1250000000),((44435898541757007244012336144024682267393352961303832529607:ℚ)/2701971837073437500000000000000000000000000000000000000000000),((547855776035564714390249399:ℚ)/2772480000000000000000000000)⟩
theorem valid20 : Valid eighth packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((3701508631:ℚ)/5000000000),((46953037:ℚ)/62500000),((-316671259:ℚ)/360468750),((-45879612203:ℚ)/58150000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2281732921:ℚ)/10000000000),((1388814178364168197421061885272616171763960479251940011:ℚ)/84469714766032241821289062500000000000000000000000000000),((114217790640845441762613:ℚ)/577600000000000000000000)⟩
theorem valid21 : Valid eighth packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((1492480671:ℚ)/2000000000),((7631256243:ℚ)/10000000000),((-51498793701:ℚ)/58150000000),((-18506248723:ℚ)/23640000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1905765873:ℚ)/10000000000),((1821886996936890212508651262668756913974693829025321155649947:ℚ)/107310976037091210937500000000000000000000000000000000000000000),((202703623:ℚ)/1024000000)⟩
theorem valid22 : Valid eighth packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/8),((-13:ℚ)/16),((3790587503:ℚ)/5000000000),((7868794989:ℚ)/10000000000),((-17720521641:ℚ)/19700000000),((-47037637539:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((70398809:ℚ)/1000000000),((3201955776042196691510260809611548562859880631866333950063:ℚ)/177802705831250000000000000000000000000000000000000000000000),((202703623:ℚ)/1024000000)⟩
theorem valid23 : Valid eighth packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((7818716283:ℚ)/10000000000),((130372901:ℚ)/156250000),((-882610307:ℚ)/953125000),((-97163311679:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((181126520726135059834125491822869326866728468239576891061:ℚ)/9089491827392578125000000000000000000000000000000000000000),((202703623:ℚ)/1024000000)⟩
theorem valid24 : Valid eighth packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((4146895787:ℚ)/5000000000),((1024408121:ℚ)/1000000000),(-1:ℚ),((-51669645231:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((640151320514814307108834226156270467:ℚ)/24000000000000000000000000000000000000),((202703623:ℚ)/1024000000)⟩
theorem valid25 : Valid eighth packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((25485053:ℚ)/25000000),((7022167113:ℚ)/5000000000),(-1:ℚ),((-320105689:ℚ)/552000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((4483628473402463533499:ℚ)/152352000000000000000000),((202703623:ℚ)/1024000000)⟩
theorem valid26 : Valid eighth packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet26 valid26
private theorem node1_3 :
    CellBound eighth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound eighth nn0 nn1 Qcell ((431:ℚ)/640) ((4367:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((4367:ℚ)/6400) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((4367:ℚ)/6400) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound eighth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound eighth nn0 nn1 Qcell ((4367:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((1781:ℚ)/2560) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound eighth nn0 nn1 Qcell ((1781:ℚ)/2560) ((8943:ℚ)/12800) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((8943:ℚ)/12800) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound eighth nn0 nn1 Qcell ((4367:ℚ)/6400) ((8943:ℚ)/12800) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((8943:ℚ)/12800) :=
  cell_join node0_6 node6_13
private theorem node14_16 :
    CellBound eighth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound eighth nn0 nn1 Qcell ((8943:ℚ)/12800) ((45:ℚ)/64) :=
  cell_join leaf13 node14_16
private theorem node16_18 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_join leaf16 leaf17
private theorem node18_20 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf18 leaf19
private theorem node16_20 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join node16_18 node18_20
private theorem node13_20 :
    CellBound eighth nn0 nn1 Qcell ((8943:ℚ)/12800) ((143:ℚ)/200) :=
  cell_join node13_16 node16_20
private theorem node21_23 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf20 node21_23
private theorem node23_25 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf23 leaf24
private theorem node25_27 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf25 leaf26
private theorem node23_27 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node23_25 node25_27
private theorem node20_27 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node20_23 node23_27
private theorem node13_27 :
    CellBound eighth nn0 nn1 Qcell ((8943:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node13_20 node20_27
private theorem node0_27 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_13 node13_27
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_27
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26]
theorem packet_count : packets.length = 27 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC03
#check @N11Formalization.C450EighthGroupedC03.bound
#print axioms N11Formalization.C450EighthGroupedC03.valid0
#print axioms N11Formalization.C450EighthGroupedC03.valid1
#print axioms N11Formalization.C450EighthGroupedC03.valid2
#print axioms N11Formalization.C450EighthGroupedC03.valid3
#print axioms N11Formalization.C450EighthGroupedC03.valid4
#print axioms N11Formalization.C450EighthGroupedC03.valid5
#print axioms N11Formalization.C450EighthGroupedC03.valid6
#print axioms N11Formalization.C450EighthGroupedC03.valid7
#print axioms N11Formalization.C450EighthGroupedC03.valid8
#print axioms N11Formalization.C450EighthGroupedC03.valid9
#print axioms N11Formalization.C450EighthGroupedC03.valid10
#print axioms N11Formalization.C450EighthGroupedC03.valid11
#print axioms N11Formalization.C450EighthGroupedC03.valid12
#print axioms N11Formalization.C450EighthGroupedC03.valid13
#print axioms N11Formalization.C450EighthGroupedC03.valid14
#print axioms N11Formalization.C450EighthGroupedC03.valid15
#print axioms N11Formalization.C450EighthGroupedC03.valid16
#print axioms N11Formalization.C450EighthGroupedC03.valid17
#print axioms N11Formalization.C450EighthGroupedC03.valid18
#print axioms N11Formalization.C450EighthGroupedC03.valid19
#print axioms N11Formalization.C450EighthGroupedC03.valid20
#print axioms N11Formalization.C450EighthGroupedC03.valid21
#print axioms N11Formalization.C450EighthGroupedC03.valid22
#print axioms N11Formalization.C450EighthGroupedC03.valid23
#print axioms N11Formalization.C450EighthGroupedC03.valid24
#print axioms N11Formalization.C450EighthGroupedC03.valid25
#print axioms N11Formalization.C450EighthGroupedC03.valid26
#print axioms N11Formalization.C450EighthGroupedC03.bound
#print axioms N11Formalization.C450EighthGroupedC03.endpoint_checks
