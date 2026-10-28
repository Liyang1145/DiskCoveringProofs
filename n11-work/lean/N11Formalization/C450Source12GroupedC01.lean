import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((6573437301:ℚ)/10000000000),((6877500003:ℚ)/10000000000),(-1:ℚ),((-18312311903:ℚ)/20600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1314483731:ℚ)/2500000000),((4517084778348651505509065822747467:ℚ)/106090000000000000000000000000000000),((233414166415129429237564907:ℚ)/591462400000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((6810994967:ℚ)/10000000000),((6996250003:ℚ)/10000000000),(-1:ℚ),((-19024984901:ℚ)/20980000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((287315449:ℚ)/625000000),((2233329804439678870863130767448271:ℚ)/55020050000000000000000000000000000),((234113772555971516970367923:ℚ)/591462400000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((6929772233:ℚ)/10000000000),((7055625003:ℚ)/10000000000),(-1:ℚ),((-19381316699:ℚ)/21170000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4231203647:ℚ)/10000000000),((4440415309043601348162214495881637:ℚ)/112042225000000000000000000000000000),((234463267106853305410734323:ℚ)/591462400000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((6989160499:ℚ)/10000000000),((7085312503:ℚ)/10000000000),(-1:ℚ),((-19559481497:ℚ)/21265000000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((252292553:ℚ)/625000000),((4427019590939876929301936481373087:ℚ)/113050056250000000000000000000000000),((234637937252261735983795707:ℚ)/591462400000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((7018854543:ℚ)/10000000000),((3557500001:ℚ)/5000000000),(-1:ℚ),((-19648563629:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((3936023433:ℚ)/10000000000),((744190574891845570669221590551351:ℚ)/19010400000000000000000000000000000),((12358715914924619819819697:ℚ)/31129600000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7048548529:ℚ)/10000000000),((3572343751:ℚ)/5000000000),(-1:ℚ),((-19737645587:ℚ)/21455000000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((3832864907:ℚ)/10000000000),((80418637443156877703335611334121:ℚ)/2054986718750000000000000000000000),((234993254665918568538407587:ℚ)/591462400000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4291:ℚ)/6400),((8601:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7078242457:ℚ)/10000000000),((1789882813:ℚ)/2500000000),(-1:ℚ),((-19826727371:ℚ)/21502500000),((1215785143:ℚ)/1250000000),((9732954333:ℚ)/10000000000),((2345108749:ℚ)/10000000000),((3726997121:ℚ)/10000000000),((1993236348023940463572145652837:ℚ)/51236425781250000000000000000000),((235080544746102781272780243:ℚ)/591462400000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((4291:ℚ)/6400) ((8601:ℚ)/12800) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((8601:ℚ)/12800),((431:ℚ)/640),(-1:ℚ),((-15:ℚ)/16),((35465447:ℚ)/50000000),((7174375003:ℚ)/10000000000),(-1:ℚ),((-99356341:ℚ)/107750000),((607479381:ℚ)/625000000),((9726281149:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((367297413:ℚ)/1000000000),((56449669806579852240001523699:ℚ)/1451257812500000000000000000000),((5879233991130376727763:ℚ)/14786560000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((8601:ℚ)/12800) ((431:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((431:ℚ)/640),((8639:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7107936329:ℚ)/10000000000),((112331543:ℚ)/156250000),(-1:ℚ),((-19915808987:ℚ)/21597500000),((4856560387:ℚ)/5000000000),((9719670101:ℚ)/10000000000),((9604357:ℚ)/40000000),((1809090887:ℚ)/5000000000),((13911809577817572603192503812733:ℚ)/357708593750000000000000000000000),((235258171318388424181414387:ℚ)/591462400000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((431:ℚ)/640) ((8639:ℚ)/12800) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8639:ℚ)/12800),((4329:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((1780695811:ℚ)/2500000000),((3602031251:ℚ)/5000000000),(-1:ℚ),((-4990087433:ℚ)/5411250000),((2426658193:ℚ)/2500000000),((9713120779:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((222661531:ℚ)/625000000),((47443439589535108832370786424999:ℚ)/1220067773437500000000000000000000),((14709186236493251280270747:ℚ)/36966400000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((8639:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4329:ℚ)/6400),((8677:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((111525471:ℚ)/156250000),((1804726563:ℚ)/2500000000),(-1:ℚ),((-625152826:ℚ)/677890625),((9700205687:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((306851119:ℚ)/1250000000),((3506143947:ℚ)/10000000000),((571741800887008037755907936423123:ℚ)/14705142382812500000000000000000000),((57479439705994230963587:ℚ)/144400000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((4329:ℚ)/6400) ((8677:ℚ)/12800) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8677:ℚ)/12800),((1087:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((7152477031:ℚ)/10000000000),((3616875001:ℚ)/5000000000),(-1:ℚ),((-20049431093:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((2425051423:ℚ)/2500000000),((2480870833:ℚ)/10000000000),((689763731:ℚ)/2000000000),((4593342524909789177489004273608983:ℚ)/118156900000000000000000000000000000),((235524587073770565808809427:ℚ)/591462400000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1087:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1087:ℚ)/1600),((1743:ℚ)/2560),(-1:ℚ),((-15:ℚ)/16),((1433464781:ℚ)/2000000000),((7248593753:ℚ)/10000000000),(-1:ℚ),((-4018794343:ℚ)/4357500000),((9687532673:ℚ)/10000000000),((2423459781:ℚ)/2500000000),((2506424897:ℚ)/10000000000),((1695281841:ℚ)/5000000000),((1255182187737954584453391491563:ℚ)/32292187500000000000000000000000),((9424535436161669856210427:ℚ)/23658496000000000000000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1743:ℚ)/2560) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1743:ℚ)/2560),((4367:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((1436434153:ℚ)/2000000000),((7263437503:ℚ)/10000000000),(-1:ℚ),((-366154769:ℚ)/397000000),((2420321489:ℚ)/2500000000),((4843766339:ℚ)/5000000000),((2531487941:ℚ)/10000000000),((1665665097:ℚ)/5000000000),((382833920707150705046134097617:ℚ)/9850562500000000000000000000000),((9428087260580229237386163:ℚ)/23658496000000000000000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((1743:ℚ)/2560) ((4367:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4367:ℚ)/6400),((8753:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7197017611:ℚ)/10000000000),((7278281253:ℚ)/10000000000),(-1:ℚ),((-20183052833:ℚ)/21882500000),((483754929:ℚ)/500000000),((9681285961:ℚ)/10000000000),((639018949:ℚ)/2500000000),((3271064971:ℚ)/10000000000),((232591510641755482282202951672783:ℚ)/5985547578125000000000000000000000),((235790973911258307625587947:ℚ)/591462400000000000000000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell ((4367:ℚ)/6400) ((8753:ℚ)/12800) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((8753:ℚ)/12800),((2193:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((1802966111:ℚ)/2500000000),((3646562501:ℚ)/5000000000),(-1:ℚ),((-5056898333:ℚ)/5482500000),((4834485079:ℚ)/5000000000),((1935019717:ℚ)/2000000000),((2580203419:ℚ)/10000000000),((128388393:ℚ)/400000000),((48660560856946740808523553861161:ℚ)/1252408593750000000000000000000000),((14742485193007292919706947:ℚ)/36966400000000000000000000)⟩
theorem valid15 : Valid source12 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source12 nn0 nn1 Qcell ((8753:ℚ)/12800) ((2193:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((2193:ℚ)/3200),((8791:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7226711263:ℚ)/10000000000),((456748047:ℚ)/625000000),(-1:ℚ),((-20272133789:ℚ)/21977500000),((9662900309:ℚ)/10000000000),((9668970163:ℚ)/10000000000),((520776989:ℚ)/2000000000),((62944019:ℚ)/200000000),((4691041316457532839115892585227477:ℚ)/120752626562500000000000000000000000),((235968549057368108422652483:ℚ)/591462400000000000000000000)⟩
theorem valid16 : Valid source12 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source12 nn0 nn1 Qcell ((2193:ℚ)/3200) ((8791:ℚ)/12800) :=
  cell_of_packet source12 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((8791:ℚ)/12800),((881:ℚ)/1280),(-1:ℚ),((-15:ℚ)/16),((7241558069:ℚ)/10000000000),((3661406251:ℚ)/5000000000),(-1:ℚ),((-20316674207:ℚ)/22025000000),((4828444327:ℚ)/5000000000),((4831450157:ℚ)/5000000000),((2627133759:ℚ)/10000000000),((3083468107:ℚ)/10000000000),((2355356310415353391560486883750439:ℚ)/60637578125000000000000000000000000),((236057331812829349857106027:ℚ)/591462400000000000000000000)⟩
theorem valid17 : Valid source12 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source12 nn0 nn1 Qcell ((8791:ℚ)/12800) ((881:ℚ)/1280) :=
  cell_of_packet source12 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((881:ℚ)/1280),((8829:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((3628202431:ℚ)/5000000000),((7337656253:ℚ)/10000000000),(-1:ℚ),((-10180607293:ℚ)/11036250000),((301591713:ℚ)/312500000),((9656888659:ℚ)/10000000000),((2649962557:ℚ)/10000000000),((94326053:ℚ)/312500000),((65700385312478389676491117996259:ℚ)/1691650195312500000000000000000000),((59036527840148887386913027:ℚ)/147865600000000000000000000)⟩
theorem valid18 : Valid source12 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source12 nn0 nn1 Qcell ((881:ℚ)/1280) ((8829:ℚ)/12800) :=
  cell_of_packet source12 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((8829:ℚ)/12800),((553:ℚ)/800),(-1:ℚ),((-15:ℚ)/16),((3635625821:ℚ)/5000000000),((7352500003:ℚ)/10000000000),(-1:ℚ),((-10202877463:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((9650934821:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((369001453:ℚ)/1250000000),((3029455782938550979306157325899:ℚ)/78012500000000000000000000000000),((59058721922125441855968987:ℚ)/147865600000000000000000000)⟩
theorem valid19 : Valid source12 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source12 nn0 nn1 Qcell ((8829:ℚ)/12800) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7286098409:ℚ)/10000000000),((3691093751:ℚ)/5000000000),(-1:ℚ),((-20450295227:ℚ)/22215000000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((576821189:ℚ)/2000000000),((267565663804427978903744553125883:ℚ)/6854253125000000000000000000000000),((236414010143756449135967667:ℚ)/591462400000000000000000000)⟩
theorem valid20 : Valid source12 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((228618497:ℚ)/312500000),((3705937501:ℚ)/5000000000),(-1:ℚ),((-641855491:ℚ)/697187500),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((685850103:ℚ)/2500000000),((37938004724684909371266617162483:ℚ)/972140820312500000000000000000000),((231046432354275831007363:ℚ)/577600000000000000000000)⟩
theorem valid21 : Valid source12 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source12 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),(-1:ℚ),((-15:ℚ)/16),((1836371337:ℚ)/2500000000),((3735625001:ℚ)/5000000000),(-1:ℚ),((-5157114011:ℚ)/5625000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2595279321:ℚ)/10000000000),((2165490091466615039293099940243:ℚ)/54931640625000000000000000000000),((779440030122155545837857:ℚ)/1945600000000000000000000)⟩
theorem valid22 : Valid source12 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((1480974417:ℚ)/2000000000),((7590000003:ℚ)/10000000000),(-1:ℚ),((-4161323251:ℚ)/4576000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((567729573:ℚ)/2500000000),((210353205982411564813007156944213:ℚ)/5234944000000000000000000000000000),((9506647018031567826919523:ℚ)/23658496000000000000000000)⟩
theorem valid23 : Valid source12 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),(-1:ℚ),((-15:ℚ)/16),((3761822487:ℚ)/5000000000),((7827500003:ℚ)/10000000000),(-1:ℚ),((-10581467461:ℚ)/11820000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1418702361:ℚ)/10000000000),((242102577576422904515916378055621:ℚ)/5821350000000000000000000000000000),((59428527780065964176322483:ℚ)/147865600000000000000000000)⟩
theorem valid24 : Valid source12 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),(-1:ℚ),((-15:ℚ)/16),((121268571:ℚ)/156250000),((4032500001:ℚ)/5000000000),(-1:ℚ),((-341805713:ℚ)/381250000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((1504514198697697656616757759167:ℚ)/36337890625000000000000000000000),((411540321:ℚ)/1024000000)⟩
theorem valid25 : Valid source12 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((39993647:ℚ)/50000000),((8540000003:ℚ)/10000000000),(-1:ℚ),((-112940941:ℚ)/129600000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((306196170899554989654902881033:ℚ)/6998400000000000000000000000000),((411540321:ℚ)/1024000000)⟩
theorem valid26 : Valid source12 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((4236901961:ℚ)/5000000000),((5220000001:ℚ)/5000000000),(-1:ℚ),((-12006705883:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3448961807687104343286912278411797:ℚ)/64000000000000000000000000000000000),((411540321:ℚ)/1024000000)⟩
theorem valid27 : Valid source12 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((10374031201:ℚ)/10000000000),((14240000003:ℚ)/10000000000),(-1:ℚ),((-29714093603:ℚ)/44160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((996970979194160450365379:ℚ)/16250880000000000000000000),((411540321:ℚ)/1024000000)⟩
theorem valid28 : Valid source12 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet28 valid28
private theorem node1_3 :
    CellBound source12 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source12 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((8601:ℚ)/12800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source12 nn0 nn1 Qcell ((2117:ℚ)/3200) ((8601:ℚ)/12800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((8601:ℚ)/12800) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source12 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source12 nn0 nn1 Qcell ((8601:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source12 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source12 nn0 nn1 Qcell ((4329:ℚ)/6400) ((4367:ℚ)/6400) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source12 nn0 nn1 Qcell ((8601:ℚ)/12800) ((4367:ℚ)/6400) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((4367:ℚ)/6400) :=
  cell_join node0_7 node7_14
private theorem node15_17 :
    CellBound source12 nn0 nn1 Qcell ((8753:ℚ)/12800) ((8791:ℚ)/12800) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source12 nn0 nn1 Qcell ((4367:ℚ)/6400) ((8791:ℚ)/12800) :=
  cell_join leaf14 node15_17
private theorem node17_19 :
    CellBound source12 nn0 nn1 Qcell ((8791:ℚ)/12800) ((8829:ℚ)/12800) :=
  cell_join leaf17 leaf18
private theorem node19_21 :
    CellBound source12 nn0 nn1 Qcell ((8829:ℚ)/12800) ((4443:ℚ)/6400) :=
  cell_join leaf19 leaf20
private theorem node17_21 :
    CellBound source12 nn0 nn1 Qcell ((8791:ℚ)/12800) ((4443:ℚ)/6400) :=
  cell_join node17_19 node19_21
private theorem node14_21 :
    CellBound source12 nn0 nn1 Qcell ((4367:ℚ)/6400) ((4443:ℚ)/6400) :=
  cell_join node14_17 node17_21
private theorem node21_23 :
    CellBound source12 nn0 nn1 Qcell ((4443:ℚ)/6400) ((45:ℚ)/64) :=
  cell_join leaf21 leaf22
private theorem node23_25 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf23 leaf24
private theorem node21_25 :
    CellBound source12 nn0 nn1 Qcell ((4443:ℚ)/6400) ((591:ℚ)/800) :=
  cell_join node21_23 node23_25
private theorem node25_27 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf25 leaf26
private theorem node27_29 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf27 leaf28
private theorem node25_29 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node25_27 node27_29
private theorem node21_29 :
    CellBound source12 nn0 nn1 Qcell ((4443:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node21_25 node25_29
private theorem node14_29 :
    CellBound source12 nn0 nn1 Qcell ((4367:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node14_21 node21_29
private theorem node0_29 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_14 node14_29
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_29
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28]
theorem packet_count : packets.length = 29 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC01
#check @N11Formalization.C450Source12GroupedC01.bound
#print axioms N11Formalization.C450Source12GroupedC01.valid0
#print axioms N11Formalization.C450Source12GroupedC01.valid1
#print axioms N11Formalization.C450Source12GroupedC01.valid2
#print axioms N11Formalization.C450Source12GroupedC01.valid3
#print axioms N11Formalization.C450Source12GroupedC01.valid4
#print axioms N11Formalization.C450Source12GroupedC01.valid5
#print axioms N11Formalization.C450Source12GroupedC01.valid6
#print axioms N11Formalization.C450Source12GroupedC01.valid7
#print axioms N11Formalization.C450Source12GroupedC01.valid8
#print axioms N11Formalization.C450Source12GroupedC01.valid9
#print axioms N11Formalization.C450Source12GroupedC01.valid10
#print axioms N11Formalization.C450Source12GroupedC01.valid11
#print axioms N11Formalization.C450Source12GroupedC01.valid12
#print axioms N11Formalization.C450Source12GroupedC01.valid13
#print axioms N11Formalization.C450Source12GroupedC01.valid14
#print axioms N11Formalization.C450Source12GroupedC01.valid15
#print axioms N11Formalization.C450Source12GroupedC01.valid16
#print axioms N11Formalization.C450Source12GroupedC01.valid17
#print axioms N11Formalization.C450Source12GroupedC01.valid18
#print axioms N11Formalization.C450Source12GroupedC01.valid19
#print axioms N11Formalization.C450Source12GroupedC01.valid20
#print axioms N11Formalization.C450Source12GroupedC01.valid21
#print axioms N11Formalization.C450Source12GroupedC01.valid22
#print axioms N11Formalization.C450Source12GroupedC01.valid23
#print axioms N11Formalization.C450Source12GroupedC01.valid24
#print axioms N11Formalization.C450Source12GroupedC01.valid25
#print axioms N11Formalization.C450Source12GroupedC01.valid26
#print axioms N11Formalization.C450Source12GroupedC01.valid27
#print axioms N11Formalization.C450Source12GroupedC01.valid28
#print axioms N11Formalization.C450Source12GroupedC01.bound
#print axioms N11Formalization.C450Source12GroupedC01.endpoint_checks
