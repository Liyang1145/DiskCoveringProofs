import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((645719291:ℚ)/1000000000),((6750140347:ℚ)/10000000000),((-44690982429:ℚ)/49600000000),((-7818350783:ℚ)/10300000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1388779469:ℚ)/2500000000),((237100173750778823552749566419445872289693:ℚ)/8090949606400000000000000000000000000000000),((3809533030819959920008016023:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((6694796517:ℚ)/10000000000),((6868933101:ℚ)/10000000000),((-45522531707:ℚ)/51500000000),((-81272354721:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4930480341:ℚ)/10000000000),((99629504137591487050714563677187313626144039138427694989793:ℚ)/3669549205099487304687500000000000000000000000000000000000000),((3816182487540718761987816647:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((425849719:ℚ)/625000000),((3493862167:ℚ)/5000000000),((-23177035169:ℚ)/26225000000),((-5176046347:ℚ)/6675000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((1147332251:ℚ)/2500000000),((217873403938168433783259481543798827853780707952915873476091:ℚ)/8036168432281347656250000000000000000000000000000000000000000),((955709342389655354800519583:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-7:ℚ)/8),((-13:ℚ)/16),((6932392747:ℚ)/10000000000),((1761779851:ℚ)/2500000000),((-3897486319:ℚ)/4450000000),((-84361105711:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2111399191:ℚ)/5000000000),((8020630096173002219218090741038177899626265303621524147903:ℚ)/306927530646093750000000000000000000000000000000000000000000),((239135427895405052955998647:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((6991790743:ℚ)/10000000000),((7076816807:ℚ)/10000000000),((-46977717649:ℚ)/53875000000),((-85133279659:ℚ)/108225000000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((40278609:ℚ)/100000000),((469926013535206001302305870790662048674678932297527853619587619:ℚ)/18315426593271862792968750000000000000000000000000000000000000000),((3827832093898415108179341503:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((702148959:ℚ)/1000000000),((1776628531:ℚ)/2500000000),((-3932133239:ℚ)/4509375000),((-8551936467:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((245435821:ℚ)/625000000),((52120883931794225707329464399065873471170789621708634665887:ℚ)/2031465347389230537414550781250000000000000000000000000000000),((239343605064819970017231367:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7051188337:ℚ)/10000000000),((1427242271:ℚ)/2000000000),((-9478695897:ℚ)/10870000000),((-85905448381:ℚ)/109175000000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((1911783101:ℚ)/5000000000),((245474710047912203657794526152070684297696139498649451489147:ℚ)/9567865261734987109375000000000000000000000000000000000000000),((153246544309584086182642927:ℚ)/591462400000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((3540443493:ℚ)/5000000000),((3582954251:ℚ)/5000000000),((-23800679757:ℚ)/27293750000),((-14381921803:ℚ)/18275000000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((743485879:ℚ)/2000000000),((158377037742224525217934974531020024202212994955471815259373:ℚ)/6173219422237263488769531250000000000000000000000000000000000),((958207468528774989211032247:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2193:ℚ)/3200),((8791:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7110585539:ℚ)/10000000000),((1795189261:ℚ)/2500000000),((-3975441609:ℚ)/4568750000),((-86677612007:ℚ)/109887500000),((9662900309:ℚ)/10000000000),((9668970163:ℚ)/10000000000),((520776989:ℚ)/2000000000),((180416067:ℚ)/500000000),((27236709009815904202577823510896550981104909858600419692097:ℚ)/1071224026175379943847656250000000000000000000000000000000000),((239603945917457269795946887:ℚ)/924160000000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((2193:ℚ)/3200) ((8791:ℚ)/12800) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8791:ℚ)/12800),((881:ℚ)/1280),((-7:ℚ)/8),((-13:ℚ)/16),((356271739:ℚ)/500000000),((1439121113:ℚ)/2000000000),((-9561847791:ℚ)/10988750000),((-4343532607:ℚ)/5506250000),((4828444327:ℚ)/5000000000),((4831450157:ℚ)/5000000000),((2627133759:ℚ)/10000000000),((3552567681:ℚ)/10000000000),((40916292274206017802867413279479612415415390267489010025629:ℚ)/1609224818900088595581054687500000000000000000000000000000000),((153379859206427623782570943:ℚ)/591462400000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((8791:ℚ)/12800) ((881:ℚ)/1280) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((881:ℚ)/1280),((8829:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7140283997:ℚ)/10000000000),((3605227033:ℚ)/5000000000),((-23956589231:ℚ)/27531250000),((-87063691961:ℚ)/110362500000),((301591713:ℚ)/312500000),((9656888659:ℚ)/10000000000),((2649962557:ℚ)/10000000000),((69919267:ℚ)/200000000),((86167629406928335236697617758335556046553504582192904111493367:ℚ)/3388906497896237754821777343750000000000000000000000000000000000),((958832477653747331976177983:ℚ)/3696640000000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((881:ℚ)/1280) ((8829:ℚ)/12800) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8829:ℚ)/12800),((553:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((715513319:ℚ)/1000000000),((7225302547:ℚ)/10000000000),((-16005705943:ℚ)/18393750000),((-8725673147:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((9650934821:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((137538651:ℚ)/400000000),((43204842889809772407198529075239324298350461573226475649779:ℚ)/1699194439758924865722656250000000000000000000000000000000000),((3836163426041864621723495623:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((8829:ℚ)/12800) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((553:ℚ)/800),((8867:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((179249559:ℚ)/250000000),((7240151007:ℚ)/10000000000),((-48121057049:ℚ)/55300000000),((-2186244267:ℚ)/2770937500),((2409799777:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((673601917:ℚ)/2500000000),((845007707:ℚ)/2500000000),((43122772883820647513709725498958428676814518834281202512923059:ℚ)/1695948843788106250000000000000000000000000000000000000000000000),((3836997026384825157128725103:ℚ)/14786560000000000000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((8867:ℚ)/12800) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((8867:ℚ)/12800),((4443:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7184831507:ℚ)/10000000000),((7254999447:ℚ)/10000000000),((-48224996129:ℚ)/55418750000),((-87642809591:ℚ)/111075000000),((4816708251:ℚ)/5000000000),((9639199113:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((1660303703:ℚ)/5000000000),((59327849755588109433983339701716748430645585465986133715224891:ℚ)/2333244827960876530456542968750000000000000000000000000000000000),((3837830711699654867898289823:ℚ)/14786560000000000000000000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((8867:ℚ)/12800) ((4443:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4443:ℚ)/6400),((1781:ℚ)/2560),((-7:ℚ)/8),((-13:ℚ)/16),((719968063:ℚ)/1000000000),((7269847867:ℚ)/10000000000),((-16109645023:ℚ)/18512500000),((-8783584819:ℚ)/11131250000),((9627690243:ℚ)/10000000000),((9633416507:ℚ)/10000000000),((2737309683:ℚ)/10000000000),((3260141923:ℚ)/10000000000),((3198199273500522356551962001881877453346659882528413512502133:ℚ)/125777532603930676269531250000000000000000000000000000000000000),((3838664481986005860428428183:ℚ)/14786560000000000000000000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell ((4443:ℚ)/6400) ((1781:ℚ)/2560) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1781:ℚ)/2560),((2231:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((7214529731:ℚ)/10000000000),((7284696267:ℚ)/10000000000),((-48432873869:ℚ)/55656250000),((-88028886503:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((1203461281:ℚ)/1250000000),((551641531:ℚ)/2000000000),((3198575207:ℚ)/10000000000),((2130823106776365664193176713037827702252910678092309760254499:ℚ)/83799418957037630677223205566406250000000000000000000000000000),((3839498337243530241583971383:ℚ)/14786560000000000000000000000)⟩
theorem valid15 : Valid tenth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound tenth nn0 nn1 Qcell ((1781:ℚ)/2560) ((2231:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7229378809:ℚ)/10000000000),((457149563:ℚ)/625000000),((-3040046941:ℚ)/3485937500),((-88221924517:ℚ)/112025000000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((3135842333:ℚ)/10000000000),((5928939898414616626704118353208153136746034350623792490433:ℚ)/231132415523365426063537597656250000000000000000000000000000),((15004555870026875058424343:ℚ)/57760000000000000000000000)⟩
theorem valid16 : Valid tenth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-7:ℚ)/8),((-13:ℚ)/16),((7259076897:ℚ)/10000000000),((7344089671:ℚ)/10000000000),((-48848627697:ℚ)/56012500000),((-29535999887:ℚ)/37500000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((601316899:ℚ)/2000000000),((845196745143572544929715051250183320145010676000312761:ℚ)/32950054922241210937500000000000000000000000000000000000),((3842834608203139853162390527:ℚ)/14786560000000000000000000000)⟩
theorem valid17 : Valid tenth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound tenth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((1457754979:ℚ)/2000000000),((460861641:ℚ)/625000000),((-3066031487:ℚ)/3515625000),((-17798814727:ℚ)/22595000000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((44870287:ℚ)/156250000),((142252182787419615782608417958558157596232502447502025315133:ℚ)/5545903805270791053771972656250000000000000000000000000000000),((15017590834646860179376607:ℚ)/57760000000000000000000000)⟩
theorem valid18 : Valid tenth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((1463694561:ℚ)/2000000000),((3701741383:ℚ)/5000000000),((-24632189681:ℚ)/28243750000),((-17876029293:ℚ)/22690000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((546069859:ℚ)/2000000000),((4648652534786101611127181918157468833618823093460923682697091:ℚ)/181240851463009490585327148437500000000000000000000000000000000),((961543059823039285818269183:ℚ)/3696640000000000000000000000)⟩
theorem valid19 : Valid tenth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((1837042657:ℚ)/2500000000),((7462875561:ℚ)/10000000000),((-49680128927:ℚ)/56725000000),((-22441554541:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2581475201:ℚ)/10000000000),((24340158386857944624904557268069024118094913556966576120477:ℚ)/933115916202894531250000000000000000000000000000000000000000),((3849511230995156100273581087:ℚ)/14786560000000000000000000000)⟩
theorem valid20 : Valid tenth packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((7407566017:ℚ)/10000000000),((3790830139:ℚ)/5000000000),((-25255810973:ℚ)/28600000000),((-90538358221:ℚ)/116300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2255120439:ℚ)/10000000000),((3995475416209098448705322173907625209664899622463819479019421:ℚ)/148319690166862500000000000000000000000000000000000000000000000),((964048324419769779105147287:ℚ)/3696640000000000000000000000)⟩
theorem valid21 : Valid tenth packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((3763177897:ℚ)/5000000000),((7700443879:ℚ)/10000000000),((-51343107153:ℚ)/58150000000),((-46041312661:ℚ)/59100000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((696624617:ℚ)/5000000000),((2887395272642766854516125950056501218597394643193465985870027:ℚ)/107310976037091210937500000000000000000000000000000000000000000),((267120877:ℚ)/1024000000)⟩
theorem valid22 : Valid tenth packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/8),((-13:ℚ)/16),((1911286073:ℚ)/2500000000),((7938007939:ℚ)/10000000000),((-17668685191:ℚ)/19700000000),((-23406718949:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((249334899802046749780545922397426466449984466359649441667:ℚ)/8744395368750000000000000000000000000000000000000000000000),((267120877:ℚ)/1024000000)⟩
theorem valid23 : Valid tenth packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((7882717689:ℚ)/10000000000),((1682624957:ℚ)/2000000000),((-11266374699:ℚ)/12200000000),((-10746147773:ℚ)/14400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((7240566946913269115643082286573531400020411772370269361:ℚ)/229818262500000000000000000000000000000000000000000000000),((267120877:ℚ)/1024000000)⟩
theorem valid24 : Valid tenth packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((2089462891:ℚ)/2500000000),((10313481137:ℚ)/10000000000),(-1:ℚ),((-25723017583:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((126649443695982838619580870890279311:ℚ)/3000000000000000000000000000000000000),((267120877:ℚ)/1024000000)⟩
theorem valid25 : Valid tenth packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((5129129923:ℚ)/5000000000),((2822779883:ℚ)/2000000000),(-1:ℚ),((-63798688999:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((141684093859799009072096423:ℚ)/3047040000000000000000000000),((267120877:ℚ)/1024000000)⟩
theorem valid26 : Valid tenth packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet26 valid26
private theorem node1_3 :
    CellBound tenth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound tenth nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound tenth nn0 nn1 Qcell ((4367:ℚ)/6400) ((8791:ℚ)/12800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((8791:ℚ)/12800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound tenth nn0 nn1 Qcell ((8791:ℚ)/12800) ((8829:ℚ)/12800) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound tenth nn0 nn1 Qcell ((8829:ℚ)/12800) ((8867:ℚ)/12800) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound tenth nn0 nn1 Qcell ((8791:ℚ)/12800) ((8867:ℚ)/12800) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((8867:ℚ)/12800) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((8867:ℚ)/12800) :=
  cell_join node0_6 node6_13
private theorem node14_16 :
    CellBound tenth nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound tenth nn0 nn1 Qcell ((8867:ℚ)/12800) ((2231:ℚ)/3200) :=
  cell_join leaf13 node14_16
private theorem node16_18 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf16 leaf17
private theorem node18_20 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_join leaf18 leaf19
private theorem node16_20 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join node16_18 node18_20
private theorem node13_20 :
    CellBound tenth nn0 nn1 Qcell ((8867:ℚ)/12800) ((2269:ℚ)/3200) :=
  cell_join node13_16 node16_20
private theorem node21_23 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf20 node21_23
private theorem node23_25 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf23 leaf24
private theorem node25_27 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf25 leaf26
private theorem node23_27 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node23_25 node25_27
private theorem node20_27 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node20_23 node23_27
private theorem node13_27 :
    CellBound tenth nn0 nn1 Qcell ((8867:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node13_20 node20_27
private theorem node0_27 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_13 node13_27
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_27
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26]
theorem packet_count : packets.length = 27 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC03
#check @N11Formalization.C450TenthGroupedC03.bound
#print axioms N11Formalization.C450TenthGroupedC03.valid0
#print axioms N11Formalization.C450TenthGroupedC03.valid1
#print axioms N11Formalization.C450TenthGroupedC03.valid2
#print axioms N11Formalization.C450TenthGroupedC03.valid3
#print axioms N11Formalization.C450TenthGroupedC03.valid4
#print axioms N11Formalization.C450TenthGroupedC03.valid5
#print axioms N11Formalization.C450TenthGroupedC03.valid6
#print axioms N11Formalization.C450TenthGroupedC03.valid7
#print axioms N11Formalization.C450TenthGroupedC03.valid8
#print axioms N11Formalization.C450TenthGroupedC03.valid9
#print axioms N11Formalization.C450TenthGroupedC03.valid10
#print axioms N11Formalization.C450TenthGroupedC03.valid11
#print axioms N11Formalization.C450TenthGroupedC03.valid12
#print axioms N11Formalization.C450TenthGroupedC03.valid13
#print axioms N11Formalization.C450TenthGroupedC03.valid14
#print axioms N11Formalization.C450TenthGroupedC03.valid15
#print axioms N11Formalization.C450TenthGroupedC03.valid16
#print axioms N11Formalization.C450TenthGroupedC03.valid17
#print axioms N11Formalization.C450TenthGroupedC03.valid18
#print axioms N11Formalization.C450TenthGroupedC03.valid19
#print axioms N11Formalization.C450TenthGroupedC03.valid20
#print axioms N11Formalization.C450TenthGroupedC03.valid21
#print axioms N11Formalization.C450TenthGroupedC03.valid22
#print axioms N11Formalization.C450TenthGroupedC03.valid23
#print axioms N11Formalization.C450TenthGroupedC03.valid24
#print axioms N11Formalization.C450TenthGroupedC03.valid25
#print axioms N11Formalization.C450TenthGroupedC03.valid26
#print axioms N11Formalization.C450TenthGroupedC03.bound
#print axioms N11Formalization.C450TenthGroupedC03.endpoint_checks
