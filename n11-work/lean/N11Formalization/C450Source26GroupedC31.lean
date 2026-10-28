import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((7:ℚ)/8),((15:ℚ)/16),((5252726669:ℚ)/10000000000),((2790350693:ℚ)/5000000000),((44449086683:ℚ)/51500000000),(1:ℚ),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1615439359:ℚ)/2000000000),((-540567144562521875243904268031219414733:ℚ)/1365908750000000000000000000000000000000),((-13343409604271962327465221:ℚ)/36966400000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((5490587777:ℚ)/10000000000),((581880057:ℚ)/1000000000),((46114114439:ℚ)/53400000000),(1:ℚ),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7634632521:ℚ)/10000000000),((-1470391489653338956230484514335561095557265309213390031:ℚ)/3717609960937500000000000000000000000000000000000000000),((-12996581254397141027849469:ℚ)/36966400000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((5728423133:ℚ)/10000000000),((1484458599:ℚ)/2500000000),((47778961931:ℚ)/54350000000),((5253375797:ℚ)/5340000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((896327249:ℚ)/1250000000),((-416458829274715761707770200179177131166138209455064438059:ℚ)/1003410549218750000000000000000000000000000000000000000000),((-12826983515651461522181029:ℚ)/36966400000000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((5847332001:ℚ)/10000000000),((1514214609:ℚ)/2500000000),((48611324007:ℚ)/55300000000),((5342643827:ℚ)/5435000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((692917263:ℚ)/1000000000),((-6845429274210136590542190353826981849261780623629766583:ℚ)/16514880566406250000000000000000000000000000000000000000),((-37961630011923343563520183:ℚ)/110899200000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((5966235399:ℚ)/10000000000),((6116366943:ℚ)/10000000000),((49443647793:ℚ)/55775000000),((21549100829:ℚ)/22120000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1670125501:ℚ)/2500000000),((-28727906527708062894047016732959540880491574513399162137:ℚ)/67776442816162109375000000000000000000000000000000000000),((-37707848060446674047731783:ℚ)/110899200000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((7:ℚ)/8),((15:ℚ)/16),((1205137027:ℚ)/2000000000),((6175873189:ℚ)/10000000000),((9971959189:ℚ)/11250000000),((21727619567:ℚ)/22310000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((819149281:ℚ)/1250000000),((-44164988208335298730704727746967919978544809707652183:ℚ)/104284286499023437500000000000000000000000000000000000),((-499312207228883651786469:ℚ)/1478656000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((6085133607:ℚ)/10000000000),((6235377229:ℚ)/10000000000),((50275935249:ℚ)/56725000000),((21906131687:ℚ)/22500000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1605936179:ℚ)/2500000000),((-1206837575912901590701524347459428275063772741872814609:ℚ)/2851960719970703125000000000000000000000000000000000000),((-37189050573769453019564167:ℚ)/110899200000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((3072290423:ℚ)/5000000000),((6294879119:ℚ)/10000000000),((25346032961:ℚ)/28600000000),((22084637357:ℚ)/22690000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1573004613:ℚ)/2500000000),((-5620156859201429337864564085863942227336397785066305779:ℚ)/13291850000000000000000000000000000000000000000000000000),((-3077479408754005637798669:ℚ)/9241600000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((7:ℚ)/8),((15:ℚ)/16),((6204026883:ℚ)/10000000000),((3162314637:ℚ)/5000000000),((51108188181:ℚ)/57437500000),((11086943911:ℚ)/11440000000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((1539466639:ℚ)/2500000000),((-506087876655937258071470967818202367351726709879418172821:ℚ)/1184313291931152343750000000000000000000000000000000000000),((-36803139920932287954823087:ℚ)/110899200000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((311687473:ℚ)/500000000),((198574341:ℚ)/312500000),((2565812311:ℚ)/2883750000),((695723023:ℚ)/717968750),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3044915071:ℚ)/5000000000),((-7502488485181581910212849264131912447466093211373:ℚ)/17564432777881622314453125000000000000000000000000),((-30561289511128812373469:ℚ)/92416000000000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2307:ℚ)/3200),((4633:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((6263471747:ℚ)/10000000000),((3192064019:ℚ)/5000000000),((51524302229:ℚ)/57912500000),((11176192057:ℚ)/11535000000),((1905827251:ℚ)/2000000000),((1907725537:ℚ)/2000000000),((3080928657:ℚ)/10000000000),((3010562039:ℚ)/5000000000),((-20732090537517216544239494187851575831442232500678726301:ℚ)/48557570379394531250000000000000000000000000000000000000),((-12181323872226342749176549:ℚ)/36966400000000000000000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4633:ℚ)/6400),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((6293193749:ℚ)/10000000000),((320693833:ℚ)/500000000),((51732356243:ℚ)/58150000000),((1122081499:ℚ)/1158250000),((9519843613:ℚ)/10000000000),((476456813:ℚ)/500000000),((622285377:ℚ)/2000000000),((2975862409:ℚ)/5000000000),((-524485256740155103083323660448206275173163132339499993147:ℚ)/1228935739843750000000000000000000000000000000000000000000),((-12138137498445035466511061:ℚ)/36966400000000000000000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1163:ℚ)/1600),((4671:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((6322915469:ℚ)/10000000000),((6443624783:ℚ)/10000000000),((51940408283:ℚ)/58387500000),((22530874349:ℚ)/23260000000),((148605427:ℚ)/156250000),((4759921809:ℚ)/5000000000),((98156347:ℚ)/312500000),((5881607473:ℚ)/10000000000),((-129570090803066429076768856720279122453728188051091507:ℚ)/303724419209361076354980468750000000000000000000000000),((-12094956675642802264783621:ℚ)/36966400000000000000000000)⟩
theorem valid12 : Valid source26 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((4671:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4671:ℚ)/6400),((469:ℚ)/640),((7:ℚ)/8),((15:ℚ)/16),((6352636909:ℚ)/10000000000),((6473372413:ℚ)/10000000000),((52148458363:ℚ)/58625000000),((22620117239:ℚ)/23355000000),((9501845013:ℚ)/10000000000),((9510747333:ℚ)/10000000000),((792422551:ℚ)/2500000000),((2905372847:ℚ)/5000000000),((-1611012001587996387163704250609745518768178494051041993161:ℚ)/3777894616699218750000000000000000000000000000000000000000),((-634304283938747566365639:ℚ)/1945600000000000000000000)⟩
theorem valid13 : Valid source26 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source26 nn0 nn1 Qcell ((4671:ℚ)/6400) ((469:ℚ)/640) :=
  cell_of_packet source26 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((3191179037:ℚ)/5000000000),((6503119557:ℚ)/10000000000),((26178253259:ℚ)/29431250000),((22709358671:ℚ)/23450000000),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((717388943:ℚ)/1250000000),((-11985445917998059485949145027146691383838045301329431409:ℚ)/28117614610290527343750000000000000000000000000000000000),((-3002152911415405712073509:ℚ)/9241600000000000000000000)⟩
theorem valid14 : Valid source26 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source26 nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((6412078967:ℚ)/10000000000),((6532866219:ℚ)/10000000000),((52564552769:ℚ)/59100000000),((22798598657:ℚ)/23545000000),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1416668843:ℚ)/2500000000),((-45810663957925465068826289320216346823667926883814244307:ℚ)/107513057812500000000000000000000000000000000000000000000),((-11965447422146515817916429:ℚ)/36966400000000000000000000)⟩
theorem valid15 : Valid source26 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source26 nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((805224949:ℚ)/1250000000),((6562612407:ℚ)/10000000000),((6596574643:ℚ)/7417187500),((22887837221:ℚ)/23640000000),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((2796702827:ℚ)/5000000000),((-1086264630718259312784161041146222994885680766227499663:ℚ)/2550338285517692565917968750000000000000000000000000000),((-186285761131432949394661:ℚ)/577600000000000000000000)⟩
theorem valid16 : Valid source26 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((129430399:ℚ)/200000000),((10547773:ℚ)/16000000),((1059612793:ℚ)/1191500000),((36763319:ℚ)/37976000),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((172477151:ℚ)/312500000),((-13503816426303342977292385806095423804468291523800291:ℚ)/31716365360156250000000000000000000000000000000000000),((-4751654204167371787261:ℚ)/14786560000000000000000)⟩
theorem valid17 : Valid source26 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source26 nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((3250620023:ℚ)/5000000000),((6651848177:ℚ)/10000000000),((26594340161:ℚ)/30025000000),((23155544531:ℚ)/23830000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((5444229111:ℚ)/10000000000),((-53423014507408370147369996106165958810740349561514527027:ℚ)/126879169995117187500000000000000000000000000000000000000),((-2947947281329355690496269:ℚ)/9241600000000000000000000)⟩
theorem valid18 : Valid source26 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source26 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((820084933:ℚ)/1250000000),((6711336417:ℚ)/10000000000),((6700594531:ℚ)/7565625000),((23334009251:ℚ)/24020000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((165352667:ℚ)/312500000),((-854171704303544403284685214482507533522584891372724297:ℚ)/2029905003690719604492187500000000000000000000000000000),((-182898617457690250537829:ℚ)/577600000000000000000000)⟩
theorem valid19 : Valid source26 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source26 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((6620117869:ℚ)/10000000000),((846352861:ℚ)/1250000000),((54020825083:ℚ)/61000000000),((2939058583:ℚ)/3026250000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((641779327:ℚ)/1250000000),((-1789786105972037698782924528056938622189423770562482445249:ℚ)/4255893750000000000000000000000000000000000000000000000000),((-11619255775227262738266821:ℚ)/36966400000000000000000000)⟩
theorem valid20 : Valid source26 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source26 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source26 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((1335911057:ℚ)/2000000000),((6889790689:ℚ)/10000000000),((10887377399:ℚ)/12390000000),((23869372067:ℚ)/24400000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2486342333:ℚ)/5000000000),((-4893745759399410501872288505125086797190706589829950919:ℚ)/11887593243750000000000000000000000000000000000000000000),((-457785367565419750476189:ℚ)/1478656000000000000000000)⟩
theorem valid21 : Valid source26 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((6798427241:ℚ)/10000000000),((3504375947:ℚ)/5000000000),((55268990687:ℚ)/62900000000),((12113127841:ℚ)/12390000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((4634178919:ℚ)/10000000000),((-479886714672254579231335690948574568153023962747554229669:ℚ)/1166522760937500000000000000000000000000000000000000000000),((-11272236331088754063412941:ℚ)/36966400000000000000000000)⟩
theorem valid22 : Valid source26 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source26 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((6917295507:ℚ)/10000000000),((7246655677:ℚ)/10000000000),((6233452061:ℚ)/7200000000),((674053163:ℚ)/680000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((4271009409:ℚ)/10000000000),((-102432136320174668325172528625594877583021843920154861:ℚ)/259200000000000000000000000000000000000000000000000000),((-32769525295564141765221967:ℚ)/110899200000000000000000000)⟩
theorem valid23 : Valid source26 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source26 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((3577510811:ℚ)/5000000000),((4099029211:ℚ)/5000000000),((28882575677:ℚ)/36200000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((3438901713:ℚ)/10000000000),((-17599651633242455016579382423550391216368198515016870431:ℚ)/55591321875000000000000000000000000000000000000000000000),((-2601813814007297141796981:ℚ)/9241600000000000000000000)⟩
theorem valid24 : Valid source26 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((405290363:ℚ)/500000000),((2287298541:ℚ)/2500000000),((3221032541:ℚ)/4000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-32499634750020448352433020877295394696879543968369389:ℚ)/100000000000000000000000000000000000000000000000000000),((-18049107:ℚ)/64000000)⟩
theorem valid25 : Valid source26 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source26 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((2264110869:ℚ)/2500000000),((2590434339:ℚ)/2000000000),((5922925361:ℚ)/9200000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-30193665330948548417777217394776587:ℚ)/194672000000000000000000000000000000),((-18049107:ℚ)/64000000)⟩
theorem valid26 : Valid source26 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet26 valid26
private theorem node1_3 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source26 nn0 nn1 Qcell ((2269:ℚ)/3200) ((919:ℚ)/1280) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((919:ℚ)/1280) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source26 nn0 nn1 Qcell ((919:ℚ)/1280) ((4633:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source26 nn0 nn1 Qcell ((4633:ℚ)/6400) ((4671:ℚ)/6400) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source26 nn0 nn1 Qcell ((919:ℚ)/1280) ((4671:ℚ)/6400) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((4671:ℚ)/6400) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((4671:ℚ)/6400) :=
  cell_join node0_6 node6_13
private theorem node14_16 :
    CellBound source26 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source26 nn0 nn1 Qcell ((4671:ℚ)/6400) ((591:ℚ)/800) :=
  cell_join leaf13 node14_16
private theorem node16_18 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_join leaf16 leaf17
private theorem node18_20 :
    CellBound source26 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf18 leaf19
private theorem node16_20 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((2421:ℚ)/3200) :=
  cell_join node16_18 node18_20
private theorem node13_20 :
    CellBound source26 nn0 nn1 Qcell ((4671:ℚ)/6400) ((2421:ℚ)/3200) :=
  cell_join node13_16 node16_20
private theorem node21_23 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound source26 nn0 nn1 Qcell ((2421:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join leaf20 node21_23
private theorem node23_25 :
    CellBound source26 nn0 nn1 Qcell ((629:ℚ)/800) ((181:ℚ)/200) :=
  cell_join leaf23 leaf24
private theorem node25_27 :
    CellBound source26 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf25 leaf26
private theorem node23_27 :
    CellBound source26 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node23_25 node25_27
private theorem node20_27 :
    CellBound source26 nn0 nn1 Qcell ((2421:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node20_23 node23_27
private theorem node13_27 :
    CellBound source26 nn0 nn1 Qcell ((4671:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node13_20 node20_27
private theorem node0_27 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_13 node13_27
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_27
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26]
theorem packet_count : packets.length = 27 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC31
#check @N11Formalization.C450Source26GroupedC31.bound
#print axioms N11Formalization.C450Source26GroupedC31.valid0
#print axioms N11Formalization.C450Source26GroupedC31.valid1
#print axioms N11Formalization.C450Source26GroupedC31.valid2
#print axioms N11Formalization.C450Source26GroupedC31.valid3
#print axioms N11Formalization.C450Source26GroupedC31.valid4
#print axioms N11Formalization.C450Source26GroupedC31.valid5
#print axioms N11Formalization.C450Source26GroupedC31.valid6
#print axioms N11Formalization.C450Source26GroupedC31.valid7
#print axioms N11Formalization.C450Source26GroupedC31.valid8
#print axioms N11Formalization.C450Source26GroupedC31.valid9
#print axioms N11Formalization.C450Source26GroupedC31.valid10
#print axioms N11Formalization.C450Source26GroupedC31.valid11
#print axioms N11Formalization.C450Source26GroupedC31.valid12
#print axioms N11Formalization.C450Source26GroupedC31.valid13
#print axioms N11Formalization.C450Source26GroupedC31.valid14
#print axioms N11Formalization.C450Source26GroupedC31.valid15
#print axioms N11Formalization.C450Source26GroupedC31.valid16
#print axioms N11Formalization.C450Source26GroupedC31.valid17
#print axioms N11Formalization.C450Source26GroupedC31.valid18
#print axioms N11Formalization.C450Source26GroupedC31.valid19
#print axioms N11Formalization.C450Source26GroupedC31.valid20
#print axioms N11Formalization.C450Source26GroupedC31.valid21
#print axioms N11Formalization.C450Source26GroupedC31.valid22
#print axioms N11Formalization.C450Source26GroupedC31.valid23
#print axioms N11Formalization.C450Source26GroupedC31.valid24
#print axioms N11Formalization.C450Source26GroupedC31.valid25
#print axioms N11Formalization.C450Source26GroupedC31.valid26
#print axioms N11Formalization.C450Source26GroupedC31.bound
#print axioms N11Formalization.C450Source26GroupedC31.endpoint_checks
