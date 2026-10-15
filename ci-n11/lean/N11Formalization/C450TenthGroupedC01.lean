import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((6498999917:ℚ)/10000000000),((6797500003:ℚ)/10000000000),(-1:ℚ),((-18344999751:ℚ)/20600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((681239687:ℚ)/1250000000),((30834292802177535105997905335510893:ℚ)/1060900000000000000000000000000000000),((921742688839912312032646817:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((6736536819:ℚ)/10000000000),((3458125001:ℚ)/5000000000),(-1:ℚ),((-19057610457:ℚ)/20980000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4813160649:ℚ)/10000000000),((15249648797840462652157623572528369:ℚ)/550200500000000000000000000000000000),((923922990545045433552017633:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((6855304267:ℚ)/10000000000),((6975625003:ℚ)/10000000000),(-1:ℚ),((-669445269:ℚ)/730000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((2231923801:ℚ)/5000000000),((36057915089380699917413049003427:ℚ)/1332250000000000000000000000000000),((925010406595658665793988017:ℚ)/2957312000000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((1728671939:ℚ)/2500000000),((3517500001:ℚ)/5000000000),(-1:ℚ),((-1632671939:ℚ)/1780000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((1069821313:ℚ)/2500000000),((321334878219656725518999779772569:ℚ)/11881500000000000000000000000000000),((57884332356139864003096513:ℚ)/184832000000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((3487035547:ℚ)/5000000000),((3532343751:ℚ)/5000000000),(-1:ℚ),((-9885106641:ℚ)/10727500000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((15964579:ℚ)/39062500),((23069916887652463931275154082266017:ℚ)/863094421875000000000000000000000000),((231672971549711117862405777:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),(-1:ℚ),((-15:ℚ)/16),((1750940677:ℚ)/2500000000),((7094375003:ℚ)/10000000000),(-1:ℚ),((-4964822031:ℚ)/5387500000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3987482553:ℚ)/10000000000),((5816976947778146286527111681149489:ℚ)/217688671875000000000000000000000000),((57953808934348030234685137:ℚ)/184832000000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((1406690857:ℚ)/2000000000),((3562031251:ℚ)/5000000000),(-1:ℚ),((-1329890857:ℚ)/1443000000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((971407001:ℚ)/2500000000),((17382816765921421926465441649693:ℚ)/650702812500000000000000000000000),((37113195428369887607855497:ℚ)/118292480000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4329:ℚ)/6400),((8677:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((3531572913:ℚ)/5000000000),((1784726563:ℚ)/2500000000),(-1:ℚ),((-10018718739:ℚ)/10846250000),((9700205687:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((306851119:ℚ)/1250000000),((3781173771:ℚ)/10000000000),((93734662625331582139872247148388277:ℚ)/3529234171875000000000000000000000000),((232025192782402355480880857:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((4329:ℚ)/6400) ((8677:ℚ)/12800) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((8677:ℚ)/12800),((1087:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((221187237:ℚ)/312500000),((3576875001:ℚ)/5000000000),(-1:ℚ),((-627561711:ℚ)/679375000),((9693839119:ℚ)/10000000000),((2425051423:ℚ)/2500000000),((2480870833:ℚ)/10000000000),((3727903547:ℚ)/10000000000),((7660655168017057261722328217113:ℚ)/288468994140625000000000000000000),((906626116026595987056657:ℚ)/2888000000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((8677:ℚ)/12800) ((1087:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1087:ℚ)/1600),((1743:ℚ)/2560),(-1:ℚ),((-15:ℚ)/16),((7092837333:ℚ)/10000000000),((7168593753:ℚ)/10000000000),(-1:ℚ),((-6708837333:ℚ)/7262500000),((9687532673:ℚ)/10000000000),((2423459781:ℚ)/2500000000),((2506424897:ℚ)/10000000000),((91847441:ℚ)/250000000),((1500547615746308018817561168430699:ℚ)/56511328125000000000000000000000000),((928669486025235661631384817:ℚ)/2957312000000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((1743:ℚ)/2560) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1743:ℚ)/2560),((4367:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7107683073:ℚ)/10000000000),((7183437503:ℚ)/10000000000),(-1:ℚ),((-20171049219:ℚ)/21835000000),((2420321489:ℚ)/2500000000),((4843766339:ℚ)/5000000000),((2531487941:ℚ)/10000000000),((723824611:ℚ)/2000000000),((7911314133477267404769358255523467:ℚ)/297979515625000000000000000000000000),((928953800731521406248950137:ℚ)/2957312000000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((1743:ℚ)/2560) ((4367:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4367:ℚ)/6400),((8753:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((1780632201:ℚ)/2500000000),((1799570313:ℚ)/2500000000),(-1:ℚ),((-5053896603:ℚ)/5470625000),((483754929:ℚ)/500000000),((9681285961:ℚ)/10000000000),((639018949:ℚ)/2500000000),((3563544287:ℚ)/10000000000),((6355862655608782599539272889403167:ℚ)/239421903125000000000000000000000000),((58077380433133959384788553:ℚ)/184832000000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((4367:ℚ)/6400) ((8753:ℚ)/12800) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((8753:ℚ)/12800),((2193:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7137374527:ℚ)/10000000000),((3606562501:ℚ)/5000000000),(-1:ℚ),((-6753374527:ℚ)/7310000000),((4834485079:ℚ)/5000000000),((1935019717:ℚ)/2000000000),((2580203419:ℚ)/10000000000),((1753561519:ℚ)/5000000000),((1772981669959144700446956347061993:ℚ)/66795125000000000000000000000000000),((929522344660374453098841337:ℚ)/2957312000000000000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((8753:ℚ)/12800) ((2193:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2193:ℚ)/3200),((8791:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7152220241:ℚ)/10000000000),((451748047:ℚ)/625000000),(-1:ℚ),((-20304660723:ℚ)/21977500000),((9662900309:ℚ)/10000000000),((9668970163:ℚ)/10000000000),((520776989:ℚ)/2000000000),((3449817913:ℚ)/10000000000),((16024163394100264213978042079305639:ℚ)/603763132812500000000000000000000000),((929806573903113544389357593:ℚ)/2957312000000000000000000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((2193:ℚ)/3200) ((8791:ℚ)/12800) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((8791:ℚ)/12800),((881:ℚ)/1280),(-1:ℚ),((-15:ℚ)/16),((7167065947:ℚ)/10000000000),((3621406251:ℚ)/5000000000),(-1:ℚ),((-20349197841:ℚ)/22025000000),((4828444327:ℚ)/5000000000),((4831450157:ℚ)/5000000000),((2627133759:ℚ)/10000000000),((3391584043:ℚ)/10000000000),((16091641680255097144742603520126201:ℚ)/606375781250000000000000000000000000),((930090774657485790870818577:ℚ)/2957312000000000000000000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell ((8791:ℚ)/12800) ((881:ℚ)/1280) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((881:ℚ)/1280),((8829:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((1795477911:ℚ)/2500000000),((7257656253:ℚ)/10000000000),(-1:ℚ),((-188830879:ℚ)/204375000),((301591713:ℚ)/312500000),((9656888659:ℚ)/10000000000),((2649962557:ℚ)/10000000000),((3332372677:ℚ)/10000000000),((14777567304398470442174287230961:ℚ)/556921875000000000000000000000000),((58148434184033613415279113:ℚ)/184832000000000000000000000)⟩
theorem valid15 : Valid tenth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound tenth nn0 nn1 Qcell ((881:ℚ)/1280) ((8829:ℚ)/12800) :=
  cell_of_packet tenth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((8829:ℚ)/12800),((553:ℚ)/800),(-1:ℚ),((-15:ℚ)/16),((7196757333:ℚ)/10000000000),((7272500003:ℚ)/10000000000),(-1:ℚ),((-20438271999:ℚ)/22120000000),((1205629803:ℚ)/1250000000),((9650934821:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3272130681:ℚ)/10000000000),((579537422865523767228656747288667:ℚ)/21843500000000000000000000000000000),((930659090723246989655544817:ℚ)/2957312000000000000000000000)⟩
theorem valid16 : Valid tenth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound tenth nn0 nn1 Qcell ((8829:ℚ)/12800) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((553:ℚ)/800),((8867:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7211603013:ℚ)/10000000000),((910917969:ℚ)/1250000000),(-1:ℚ),((-20482809039:ℚ)/22167500000),((2409799777:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((673601917:ℚ)/2500000000),((3210799983:ℚ)/10000000000),((32589951239328627554908398133577239:ℚ)/1228495140625000000000000000000000000),((930943205994591799908408657:ℚ)/2957312000000000000000000000)⟩
theorem valid17 : Valid tenth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((8867:ℚ)/12800) :=
  cell_of_packet tenth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((8867:ℚ)/12800),((4443:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((3613224343:ℚ)/5000000000),((3651093751:ℚ)/5000000000),(-1:ℚ),((-3421224343:ℚ)/3702500000),((4816708251:ℚ)/5000000000),((9639199113:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3148316881:ℚ)/10000000000),((2727175521167494166393026133282287:ℚ)/102813796875000000000000000000000000),((232806823199224837939737097:ℚ)/739328000000000000000000000)⟩
theorem valid18 : Valid tenth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound tenth nn0 nn1 Qcell ((8867:ℚ)/12800) ((4443:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((4443:ℚ)/6400),((1781:ℚ)/2560),(-1:ℚ),((-15:ℚ)/16),((144825887:ℚ)/200000000),((1829257813:ℚ)/2500000000),(-1:ℚ),((-411437661:ℚ)/445250000),((9627690243:ℚ)/10000000000),((9633416507:ℚ)/10000000000),((2737309683:ℚ)/10000000000),((1542305643:ℚ)/5000000000),((52580097047931454182449935482151:ℚ)/1982475625000000000000000000000000),((372604540444804195462457:ℚ)/1182924800000000000000000)⟩
theorem valid19 : Valid tenth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound tenth nn0 nn1 Qcell ((4443:ℚ)/6400) ((1781:ℚ)/2560) :=
  cell_of_packet tenth nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((1781:ℚ)/2560),((2231:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((3628070003:ℚ)/5000000000),((3665937501:ℚ)/5000000000),(-1:ℚ),((-10308210009:ℚ)/11155000000),((2405504993:ℚ)/2500000000),((1203461281:ℚ)/1250000000),((551641531:ℚ)/2000000000),((12078423:ℚ)/40000000),((2062457146086779537256070037105159:ℚ)/77771265625000000000000000000000000),((232948845234759715131678177:ℚ)/739328000000000000000000000)⟩
theorem valid20 : Valid tenth packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound tenth nn0 nn1 Qcell ((1781:ℚ)/2560) ((2231:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7270985653:ℚ)/10000000000),((7361562503:ℚ)/10000000000),(-1:ℚ),((-20660956959:ℚ)/22405000000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((590642873:ℚ)/2000000000),((6690781663492515809772206756655659:ℚ)/250992012500000000000000000000000000),((932377325707042606051667377:ℚ)/2957312000000000000000000000)⟩
theorem valid21 : Valid tenth packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),(-1:ℚ),((-15:ℚ)/16),((292027077:ℚ)/400000000),((3695625001:ℚ)/5000000000),(-1:ℚ),((-92222359:ℚ)/100000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((281587961:ℚ)/1000000000),((41641868100624770505415266827:ℚ)/1562500000000000000000000000000),((1492712388641651181753937:ℚ)/4731699200000000000000000)⟩
theorem valid22 : Valid tenth packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound tenth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((1832592041:ℚ)/2500000000),((7450625003:ℚ)/10000000000),(-1:ℚ),((-5209776123:ℚ)/5672500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1335845439:ℚ)/5000000000),((433094586325545939997727036398651:ℚ)/16088628125000000000000000000000000),((58381808312532444211360393:ℚ)/184832000000000000000000000)⟩
theorem valid23 : Valid tenth packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((147795011:ℚ)/200000000),((7510000003:ℚ)/10000000000),(-1:ℚ),((-420345033:ℚ)/457600000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2357664267:ℚ)/10000000000),((14083839005337292108577168783707:ℚ)/523494400000000000000000000000000),((374097679068097115499713:ℚ)/1182924800000000000000000)⟩
theorem valid24 : Valid tenth packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((1862283203:ℚ)/2500000000),((7628750003:ℚ)/10000000000),(-1:ℚ),((-5298849609:ℚ)/5815000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1995844303:ℚ)/10000000000),((6952324492954356633172901445038257:ℚ)/253606687500000000000000000000000000),((58562106923019610057955777:ℚ)/184832000000000000000000000)⟩
theorem valid25 : Valid tenth packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),(-1:ℚ),((-15:ℚ)/16),((7567896981:ℚ)/10000000000),((7747500003:ℚ)/10000000000),(-1:ℚ),((-7183896981:ℚ)/7880000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((459731369:ℚ)/5000000000),((6373909052209971787813836284519339:ℚ)/232854000000000000000000000000000000),((936878413809367525773304433:ℚ)/2957312000000000000000000000)⟩
theorem valid26 : Valid tenth packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),(-1:ℚ),((-15:ℚ)/16),((3843330347:ℚ)/5000000000),((3992500001:ℚ)/5000000000),(-1:ℚ),((-10953991041:ℚ)/12200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((517885179923676519066563831564449:ℚ)/18300000000000000000000000000000000),((324392983:ℚ)/1024000000)⟩
theorem valid27 : Valid tenth packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((7924186839:ℚ)/10000000000),((8460000003:ℚ)/10000000000),(-1:ℚ),((-2513395613:ℚ)/2880000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((620179754273997412523335091754473:ℚ)/20736000000000000000000000000000000),((324392983:ℚ)/1024000000)⟩
theorem valid28 : Valid tenth packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((8399234529:ℚ)/10000000000),((5180000001:ℚ)/5000000000),(-1:ℚ),((-24045703587:ℚ)/32000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((282895666366444812370792763823722521:ℚ)/7680000000000000000000000000000000000),((324392983:ℚ)/1024000000)⟩
theorem valid29 : Valid tenth packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet29 valid29
def packet30 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((5149689989:ℚ)/5000000000),((14160000003:ℚ)/10000000000),(-1:ℚ),((-4957689989:ℚ)/7360000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((567565866411125835701183:ℚ)/13542400000000000000000000),((324392983:ℚ)/1024000000)⟩
theorem valid30 : Valid tenth packet30 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf30 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet30 valid30
private theorem node1_3 :
    CellBound tenth nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound tenth nn0 nn1 Qcell ((2117:ℚ)/3200) ((4291:ℚ)/6400) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound tenth nn0 nn1 Qcell ((4291:ℚ)/6400) ((4329:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound tenth nn0 nn1 Qcell ((2117:ℚ)/3200) ((4329:ℚ)/6400) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((4329:ℚ)/6400) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound tenth nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound tenth nn0 nn1 Qcell ((4329:ℚ)/6400) ((4367:ℚ)/6400) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound tenth nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound tenth nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound tenth nn0 nn1 Qcell ((4367:ℚ)/6400) ((881:ℚ)/1280) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound tenth nn0 nn1 Qcell ((4329:ℚ)/6400) ((881:ℚ)/1280) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((881:ℚ)/1280) :=
  cell_join node0_7 node7_15
private theorem node15_17 :
    CellBound tenth nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_join leaf15 leaf16
private theorem node17_19 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_join leaf17 leaf18
private theorem node15_19 :
    CellBound tenth nn0 nn1 Qcell ((881:ℚ)/1280) ((4443:ℚ)/6400) :=
  cell_join node15_17 node17_19
private theorem node19_21 :
    CellBound tenth nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_join leaf19 leaf20
private theorem node21_23 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf21 leaf22
private theorem node19_23 :
    CellBound tenth nn0 nn1 Qcell ((4443:ℚ)/6400) ((45:ℚ)/64) :=
  cell_join node19_21 node21_23
private theorem node15_23 :
    CellBound tenth nn0 nn1 Qcell ((881:ℚ)/1280) ((45:ℚ)/64) :=
  cell_join node15_19 node19_23
private theorem node23_25 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf23 leaf24
private theorem node25_27 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf25 leaf26
private theorem node23_27 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join node23_25 node25_27
private theorem node27_29 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf27 leaf28
private theorem node29_31 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf29 leaf30
private theorem node27_31 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node27_29 node29_31
private theorem node23_31 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node23_27 node27_31
private theorem node15_31 :
    CellBound tenth nn0 nn1 Qcell ((881:ℚ)/1280) ((69:ℚ)/50) :=
  cell_join node15_23 node23_31
private theorem node0_31 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_15 node15_31
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_31
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29,packet30]
theorem packet_count : packets.length = 31 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC01
#check @N11Formalization.C450TenthGroupedC01.bound
#print axioms N11Formalization.C450TenthGroupedC01.valid0
#print axioms N11Formalization.C450TenthGroupedC01.valid1
#print axioms N11Formalization.C450TenthGroupedC01.valid2
#print axioms N11Formalization.C450TenthGroupedC01.valid3
#print axioms N11Formalization.C450TenthGroupedC01.valid4
#print axioms N11Formalization.C450TenthGroupedC01.valid5
#print axioms N11Formalization.C450TenthGroupedC01.valid6
#print axioms N11Formalization.C450TenthGroupedC01.valid7
#print axioms N11Formalization.C450TenthGroupedC01.valid8
#print axioms N11Formalization.C450TenthGroupedC01.valid9
#print axioms N11Formalization.C450TenthGroupedC01.valid10
#print axioms N11Formalization.C450TenthGroupedC01.valid11
#print axioms N11Formalization.C450TenthGroupedC01.valid12
#print axioms N11Formalization.C450TenthGroupedC01.valid13
#print axioms N11Formalization.C450TenthGroupedC01.valid14
#print axioms N11Formalization.C450TenthGroupedC01.valid15
#print axioms N11Formalization.C450TenthGroupedC01.valid16
#print axioms N11Formalization.C450TenthGroupedC01.valid17
#print axioms N11Formalization.C450TenthGroupedC01.valid18
#print axioms N11Formalization.C450TenthGroupedC01.valid19
#print axioms N11Formalization.C450TenthGroupedC01.valid20
#print axioms N11Formalization.C450TenthGroupedC01.valid21
#print axioms N11Formalization.C450TenthGroupedC01.valid22
#print axioms N11Formalization.C450TenthGroupedC01.valid23
#print axioms N11Formalization.C450TenthGroupedC01.valid24
#print axioms N11Formalization.C450TenthGroupedC01.valid25
#print axioms N11Formalization.C450TenthGroupedC01.valid26
#print axioms N11Formalization.C450TenthGroupedC01.valid27
#print axioms N11Formalization.C450TenthGroupedC01.valid28
#print axioms N11Formalization.C450TenthGroupedC01.valid29
#print axioms N11Formalization.C450TenthGroupedC01.valid30
#print axioms N11Formalization.C450TenthGroupedC01.bound
#print axioms N11Formalization.C450TenthGroupedC01.endpoint_checks
