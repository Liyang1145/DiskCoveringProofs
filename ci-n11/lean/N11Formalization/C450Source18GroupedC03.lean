import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((670876401:ℚ)/1000000000),((1726292127:ℚ)/2500000000),((-10804044889:ℚ)/12400000000),((-7633393213:ℚ)/10110000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((305719369:ℚ)/625000000),((6194900143256016929108143290183521912051:ℚ)/81200017896000000000000000000000000000000),((3138966340645071158624353:ℚ)/5776000000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((6827725543:ℚ)/10000000000),((878009627:ℚ)/1250000000),((-5506067389:ℚ)/6318750000),((-77880432059:ℚ)/103000000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((4547179569:ℚ)/10000000000),((637002698628805915616961438678053205579772418069424899257:ℚ)/8364076376021575927734375000000000000000000000000000000000),((2180207289123204933073:ℚ)/4000000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((6946679253:ℚ)/10000000000),((3541764547:ℚ)/5000000000),((-22232351829:ℚ)/25750000000),((-79426830289:ℚ)/103950000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((2088347523:ℚ)/5000000000),((66676884757737336458237856335556755055095869629972606948409:ℚ)/915145523547363281250000000000000000000000000000000000000000),((12611385396445361863775913:ℚ)/23104000000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((1751538327:ℚ)/2500000000),((1422650921:ℚ)/2000000000),((-8934556447:ℚ)/10395000000),((-20049998251:ℚ)/26106250000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((3979373257:ℚ)/10000000000),((99194123851201173930516880465673697265021967799301298659631:ℚ)/1391873533268615332031250000000000000000000000000000000000000),((2019302396767183538690737:ℚ)/3696640000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((3517944829:ℚ)/5000000000),((1785744943:ℚ)/2500000000),((-11220214601:ℚ)/13053125000),((-40293282777:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3877161113:ℚ)/10000000000),((68129630476025607813886775950704554719950110983623405947281:ℚ)/955992536915378963947296142578125000000000000000000000000000),((3157473730755739757424193:ℚ)/5776000000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-7:ℚ)/8),((-13:ℚ)/16),((1766406391:ℚ)/2500000000),((7172704599:ℚ)/10000000000),((-45088932193:ℚ)/52450000000),((-20243283083:ℚ)/26343750000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((3772325711:ℚ)/10000000000),((228358725521860507497533600358802112342734521867257719087979:ℚ)/3204362558168753906250000000000000000000000000000000000000000),((50556600909435324308596657:ℚ)/92416000000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((843:ℚ)/1280),((8449:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((3547680517:ℚ)/5000000000),((3593783443:ℚ)/5000000000),((-7532161367:ℚ)/8781250000),((-40679846721:ℚ)/52806250000),((4890720817:ℚ)/5000000000),((1957725423:ℚ)/2000000000),((83782417:ℚ)/400000000),((3664641411:ℚ)/10000000000),((2661943019506804758166620719779976244006736638217736665708101:ℚ)/37763277096692109107971191406250000000000000000000000000000000),((35024315831713491156513:ℚ)/64000000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((843:ℚ)/1280) ((8449:ℚ)/12800) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((8449:ℚ)/12800),((2117:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((3555114303:ℚ)/5000000000),((720242909:ℚ)/1000000000),((-4529700363:ℚ)/5280625000),((-40776485939:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((9781441639:ℚ)/10000000000),((425706267:ℚ)/2000000000),((902412839:ℚ)/2500000000),((20767779856501550102428868304621373021839965066757312339127:ℚ)/294611489678518236541748046875000000000000000000000000000000),((505936235761281930871017:ℚ)/924160000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((8449:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2117:ℚ)/3200),((8487:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7125096071:ℚ)/10000000000),((7217291211:ℚ)/10000000000),((-45401038477:ℚ)/52925000000),((-9082916547:ℚ)/11787500000),((9767266893:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((2161672951:ℚ)/10000000000),((3553848741:ℚ)/10000000000),((87122158941217635507236811226773189357346959714991379164523957:ℚ)/1235882725506538623046875000000000000000000000000000000000000000),((50612135454829236623772697:ℚ)/92416000000000000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((2117:ℚ)/3200) ((8487:ℚ)/12800) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8487:ℚ)/12800),((4253:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((713996343:ℚ)/1000000000),((7232153249:ℚ)/10000000000),((-369959941:ℚ)/431250000),((-8193952459:ℚ)/10632500000),((9760276751:ℚ)/10000000000),((4883633449:ℚ)/5000000000),((438804929:ℚ)/2000000000),((874298651:ℚ)/2500000000),((106529248929882759031712008342704671338498703054366485909:ℚ)/1511147498723602294921875000000000000000000000000000000000),((50630647697089588627593057:ℚ)/92416000000000000000000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((8487:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4253:ℚ)/6400),((341:ℚ)/512),((-7:ℚ)/8),((-13:ℚ)/16),((7154830683:ℚ)/10000000000),((7247015207:ℚ)/10000000000),((-45609106449:ℚ)/53162500000),((-82132798879:ℚ)/106562500000),((195067017:ℚ)/200000000),((2440069189:ℚ)/2500000000),((1112811311:ℚ)/5000000000),((687929361:ℚ)/2000000000),((1539597782112266136801446629375143737168449627191126457563:ℚ)/21839111125663664550781250000000000000000000000000000000000),((140302383120881952964713:ℚ)/256000000000000000000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((4253:ℚ)/6400) ((341:ℚ)/512) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((341:ℚ)/512),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((7169697831:ℚ)/10000000000),((7261877083:ℚ)/10000000000),((-45713139581:ℚ)/53281250000),((-82326071803:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((1950670171:ℚ)/2000000000),((2256500263:ℚ)/10000000000),((676231929:ℚ)/2000000000),((4751251879248404028402207812802452479051036661661077496862241:ℚ)/67394701654171943664550781250000000000000000000000000000000000),((140353665598273453026193:ℚ)/256000000000000000000000)⟩
theorem valid11 : Valid source18 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source18 nn0 nn1 Qcell ((341:ℚ)/512) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((267:ℚ)/400),((8563:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((57476519:ℚ)/80000000),((3638369439:ℚ)/5000000000),((-22908586073:ℚ)/26700000000),((-660154747:ℚ)/856300000),((9739690061:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((1143344217:ℚ)/5000000000),((664336687:ℚ)/2000000000),((102495876058523433064213369104110938941804727316901241214500073:ℚ)/1453832720745778125000000000000000000000000000000000000000000000),((12671546655335642557680097:ℚ)/23104000000000000000000000)⟩
theorem valid12 : Valid source18 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((8563:ℚ)/12800) :=
  cell_of_packet source18 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((8563:ℚ)/12800),((4291:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((1439886363:ℚ)/2000000000),((7291600593:ℚ)/10000000000),((-45921204151:ℚ)/53518750000),((-16542522719:ℚ)/21455000000),((1216619291:ℚ)/1250000000),((4869845033:ℚ)/5000000000),((1158107867:ℚ)/5000000000),((1630581997:ℚ)/5000000000),((9716419170375091874762071015800531414630819682984434654024173:ℚ)/137817688269896096074581146240234375000000000000000000000000000),((50704700328974058834892993:ℚ)/92416000000000000000000000)⟩
theorem valid13 : Valid source18 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source18 nn0 nn1 Qcell ((8563:ℚ)/12800) ((4291:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4291:ℚ)/6400),((8601:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((1803574663:ℚ)/2500000000),((7306462229:ℚ)/10000000000),((-46025235603:ℚ)/53637500000),((-20726470619:ℚ)/26878125000),((1215785143:ℚ)/1250000000),((9732954333:ℚ)/10000000000),((2345108749:ℚ)/10000000000),((3199542053:ℚ)/10000000000),((836153390386547858685127641409137903790814803072638380566687:ℚ)/11859753642588910388946533203125000000000000000000000000000000),((50723214405109420816402137:ℚ)/92416000000000000000000000)⟩
theorem valid14 : Valid source18 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source18 nn0 nn1 Qcell ((4291:ℚ)/6400) ((8601:ℚ)/12800) :=
  cell_of_packet source18 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((8601:ℚ)/12800),((431:ℚ)/640),((-7:ℚ)/8),((-13:ℚ)/16),((7229165387:ℚ)/10000000000),((3660661893:ℚ)/5000000000),((-23064633251:ℚ)/26878125000),((-83099150031:ℚ)/107750000000),((607479381:ℚ)/625000000),((9726281149:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((784188141:ℚ)/2500000000),((74506080831468553680071735600110636667631824328662375471447:ℚ)/1056751192148025879263877868652343750000000000000000000000000),((12685432212435302557025593:ℚ)/23104000000000000000000000)⟩
theorem valid15 : Valid source18 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source18 nn0 nn1 Qcell ((8601:ℚ)/12800) ((431:ℚ)/640) :=
  cell_of_packet source18 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((362201601:ℚ)/500000000),((1470209333:ℚ)/2000000000),((-9267465331:ℚ)/10775000000),((-4164620813:ℚ)/5411250000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((3072723881:ℚ)/10000000000),((326272596543945067501397354843753328884325431297478619746817:ℚ)/4578856648317965698242187500000000000000000000000000000000000),((2031150353878241346267673:ℚ)/3696640000000000000000000)⟩
theorem valid16 : Valid source18 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source18 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((1454752997:ℚ)/2000000000),((3690384617:ℚ)/5000000000),((-23272692319:ℚ)/27056250000),((-16735788961:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2940623287:ℚ)/10000000000),((46946225898954198012969334414114730087113574075660734605703:ℚ)/658853626180290985107421875000000000000000000000000000000000),((12703947581385770620180273:ℚ)/23104000000000000000000000)⟩
theorem valid17 : Valid source18 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source18 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7303497551:ℚ)/10000000000),((7410491497:ℚ)/10000000000),((-46753440479:ℚ)/54350000000),((-84065468163:ℚ)/109175000000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((1401246377:ℚ)/5000000000),((42608294459646541705174101730240118493184829129650446002112813:ℚ)/597991578858436694335937500000000000000000000000000000000000000),((50852823290427916011166513:ℚ)/92416000000000000000000000)⟩
theorem valid18 : Valid source18 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((293329189:ℚ)/400000000),((7440213459:ℚ)/10000000000),((-46961494213:ℚ)/54587500000),((-3378079457:ℚ)/4386000000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((332173933:ℚ)/1250000000),((43544417505700470514614293277787766626043868590946015178694839:ℚ)/611148722801489085388183593750000000000000000000000000000000000),((50889857747783160935127817:ℚ)/92416000000000000000000000)⟩
theorem valid19 : Valid source18 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source18 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((736296151:ℚ)/1000000000),((7499656493:ℚ)/10000000000),((-15792531817:ℚ)/18275000000),((-8483849963:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((626026813:ℚ)/2500000000),((2839868346818361966691227820102496941658275097097788049791:ℚ)/39058510904198455810546875000000000000000000000000000000000),((50963931155878368011414793:ℚ)/92416000000000000000000000)⟩
theorem valid20 : Valid source18 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source18 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-7:ℚ)/8),((-13:ℚ)/16),((3711211969:ℚ)/5000000000),((1904634777:ℚ)/2500000000),((-12052443439:ℚ)/13825000000),((-14268585199:ℚ)/18750000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((541489057:ℚ)/2500000000),((3385055229881731504299021761284619233767247456895447:ℚ)/44796240234375000000000000000000000000000000000000000),((17690093:ℚ)/32000000)⟩
theorem valid21 : Valid source18 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source18 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((7541344353:ℚ)/10000000000),((773741731:ℚ)/1000000000),((-4904192117:ℚ)/5625000000),((-87157476589:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1243205239:ℚ)/10000000000),((858211920017287589658912051481639103425135572746868408851:ℚ)/11373383331298828125000000000000000000000000000000000000000),((17690093:ℚ)/32000000)⟩
theorem valid22 : Valid source18 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((957532387:ℚ)/1250000000),((8688307423:ℚ)/10000000000),((-55698151961:ℚ)/57200000000),((-3695973677:ℚ)/5400000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((4041094028225578979351709538670228911331987658222030204481:ℚ)/35529115050000000000000000000000000000000000000000000000000),((17690093:ℚ)/32000000)⟩
theorem valid23 : Valid source18 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((4305701421:ℚ)/5000000000),((1323697473:ℚ)/1250000000),(-1:ℚ),((-50534118473:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3059105047213184013936487362256608593:ℚ)/24000000000000000000000000000000000000),((17690093:ℚ)/32000000)⟩
theorem valid24 : Valid source18 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((5256518787:ℚ)/5000000000),((14391072813:ℚ)/10000000000),(-1:ℚ),((-2734554097:ℚ)/4800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1628725179066047856665081:ℚ)/11520000000000000000000000),((17690093:ℚ)/32000000)⟩
theorem valid25 : Valid source18 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet25 valid25
private theorem node1_3 :
    CellBound source18 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2079:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source18 nn0 nn1 Qcell ((4177:ℚ)/6400) ((843:ℚ)/1280) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source18 nn0 nn1 Qcell ((2079:ℚ)/3200) ((843:ℚ)/1280) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((843:ℚ)/1280) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source18 nn0 nn1 Qcell ((8449:ℚ)/12800) ((8487:ℚ)/12800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source18 nn0 nn1 Qcell ((843:ℚ)/1280) ((8487:ℚ)/12800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source18 nn0 nn1 Qcell ((8487:ℚ)/12800) ((341:ℚ)/512) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source18 nn0 nn1 Qcell ((341:ℚ)/512) ((8563:ℚ)/12800) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source18 nn0 nn1 Qcell ((8487:ℚ)/12800) ((8563:ℚ)/12800) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source18 nn0 nn1 Qcell ((843:ℚ)/1280) ((8563:ℚ)/12800) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((8563:ℚ)/12800) :=
  cell_join node0_6 node6_13
private theorem node14_16 :
    CellBound source18 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source18 nn0 nn1 Qcell ((8563:ℚ)/12800) ((431:ℚ)/640) :=
  cell_join leaf13 node14_16
private theorem node17_19 :
    CellBound source18 nn0 nn1 Qcell ((4329:ℚ)/6400) ((4367:ℚ)/6400) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source18 nn0 nn1 Qcell ((431:ℚ)/640) ((4367:ℚ)/6400) :=
  cell_join leaf16 node17_19
private theorem node13_19 :
    CellBound source18 nn0 nn1 Qcell ((8563:ℚ)/12800) ((4367:ℚ)/6400) :=
  cell_join node13_16 node16_19
private theorem node20_22 :
    CellBound source18 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound source18 nn0 nn1 Qcell ((4367:ℚ)/6400) ((45:ℚ)/64) :=
  cell_join leaf19 node20_22
private theorem node22_24 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((81:ℚ)/100) :=
  cell_join leaf22 leaf23
private theorem node24_26 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf24 leaf25
private theorem node22_26 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node22_24 node24_26
private theorem node19_26 :
    CellBound source18 nn0 nn1 Qcell ((4367:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node19_22 node22_26
private theorem node13_26 :
    CellBound source18 nn0 nn1 Qcell ((8563:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node13_19 node19_26
private theorem node0_26 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_13 node13_26
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_26
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25]
theorem packet_count : packets.length = 26 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC03
#check @N11Formalization.C450Source18GroupedC03.bound
#print axioms N11Formalization.C450Source18GroupedC03.valid0
#print axioms N11Formalization.C450Source18GroupedC03.valid1
#print axioms N11Formalization.C450Source18GroupedC03.valid2
#print axioms N11Formalization.C450Source18GroupedC03.valid3
#print axioms N11Formalization.C450Source18GroupedC03.valid4
#print axioms N11Formalization.C450Source18GroupedC03.valid5
#print axioms N11Formalization.C450Source18GroupedC03.valid6
#print axioms N11Formalization.C450Source18GroupedC03.valid7
#print axioms N11Formalization.C450Source18GroupedC03.valid8
#print axioms N11Formalization.C450Source18GroupedC03.valid9
#print axioms N11Formalization.C450Source18GroupedC03.valid10
#print axioms N11Formalization.C450Source18GroupedC03.valid11
#print axioms N11Formalization.C450Source18GroupedC03.valid12
#print axioms N11Formalization.C450Source18GroupedC03.valid13
#print axioms N11Formalization.C450Source18GroupedC03.valid14
#print axioms N11Formalization.C450Source18GroupedC03.valid15
#print axioms N11Formalization.C450Source18GroupedC03.valid16
#print axioms N11Formalization.C450Source18GroupedC03.valid17
#print axioms N11Formalization.C450Source18GroupedC03.valid18
#print axioms N11Formalization.C450Source18GroupedC03.valid19
#print axioms N11Formalization.C450Source18GroupedC03.valid20
#print axioms N11Formalization.C450Source18GroupedC03.valid21
#print axioms N11Formalization.C450Source18GroupedC03.valid22
#print axioms N11Formalization.C450Source18GroupedC03.valid23
#print axioms N11Formalization.C450Source18GroupedC03.valid24
#print axioms N11Formalization.C450Source18GroupedC03.valid25
#print axioms N11Formalization.C450Source18GroupedC03.bound
#print axioms N11Formalization.C450Source18GroupedC03.endpoint_checks
