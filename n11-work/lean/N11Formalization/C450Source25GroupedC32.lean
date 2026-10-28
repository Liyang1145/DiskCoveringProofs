import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((15:ℚ)/16),(1:ℚ),((2619999999:ℚ)/5000000000),((1113406879:ℚ)/2000000000),((9331999997:ℚ)/10300000000),(1:ℚ),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((4050170849:ℚ)/5000000000),((-3021404465738541847261760164434891875827913275524152903:ℚ)/6829543750000000000000000000000000000000000000000000000),((-46207533842627673240400323:ℚ)/147865600000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((2738749999:ℚ)/5000000000),((1451204537:ℚ)/2500000000),((9688249997:ℚ)/10680000000),(1:ℚ),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((95743829:ℚ)/125000000),((-280538655600815694024401426035331649401503811046411181:ℚ)/634472100000000000000000000000000000000000000000000000),((-44643317115865048891900323:ℚ)/147865600000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((2857499999:ℚ)/5000000000),((1480925643:ℚ)/2500000000),((10044499997:ℚ)/10870000000),(1:ℚ),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((899681561:ℚ)/1250000000),((-3720214543108275367394029901060836197156164791041932543:ℚ)/8027284393750000000000000000000000000000000000000000000),((-43999929204352300791400323:ℚ)/147865600000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((2916874999:ℚ)/5000000000),((604258237:ℚ)/1000000000),((10222624997:ℚ)/11060000000),(1:ℚ),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((6957102353:ℚ)/10000000000),((-61159026355423069908512196814638319578540779712323567:ℚ)/132119044531250000000000000000000000000000000000000000),((-43227792301947395134150323:ℚ)/147865600000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2976249999:ℚ)/5000000000),((11918009:ℚ)/19531250),((10400749997:ℚ)/11155000000),(1:ℚ),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1341924743:ℚ)/2000000000),((-256547320516338535188434688971384363319121064052352687:ℚ)/542211542529296875000000000000000000000000000000000000),((-42913185220662783946900323:ℚ)/147865600000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((15:ℚ)/16),(1:ℚ),((3005937499:ℚ)/5000000000),((6161457777:ℚ)/10000000000),((10489812497:ℚ)/11250000000),(1:ℚ),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3291477151:ℚ)/5000000000),((-16435069541975564036125349980527669325212570391374683:ℚ)/34761428833007812500000000000000000000000000000000000),((-42529607419174055659525323:ℚ)/147865600000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3035624999:ℚ)/5000000000),((3110446951:ℚ)/5000000000),((10578874997:ℚ)/11345000000),(1:ℚ),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6454175219:ℚ)/10000000000),((-10779443442061355997318751813165398171151703406552287:ℚ)/22815685759765625000000000000000000000000000000000000),((-42146743251397300637650323:ℚ)/147865600000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3065312499:ℚ)/5000000000),((3125305791:ℚ)/5000000000),((1523991071:ℚ)/1627500000),(1:ℚ),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((3161577457:ℚ)/5000000000),((-4287825657957229893326861688226882471312719407372543:ℚ)/8980939160156250000000000000000000000000000000000000),((-41991920484768359393275323:ℚ)/147865600000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3080156249:ℚ)/5000000000),((6280329011:ℚ)/10000000000),((10712468747:ℚ)/11440000000),(1:ℚ),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((391047473:ℚ)/625000000),((-4465833327908032365269140107458494689990887609344174193:ℚ)/9357462400000000000000000000000000000000000000000000000),((-41801110688475479129650323:ℚ)/147865600000000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((15:ℚ)/16),(1:ℚ),((3094999999:ℚ)/5000000000),((394377887:ℚ)/625000000),((10756999997:ℚ)/11487500000),(1:ℚ),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((193429637:ℚ)/312500000),((-4519949745294918848575086878429011085161945359625243967:ℚ)/9474506335449218750000000000000000000000000000000000000),((-41610479201165119926400323:ℚ)/147865600000000000000000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3109843749:ℚ)/5000000000),((6339763129:ℚ)/10000000000),((10801531247:ℚ)/11535000000),(1:ℚ),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((6122100807:ℚ)/10000000000),((-178692348871892595300926188666661858202034623820877:ℚ)/374707899261474609375000000000000000000000000000000),((-41420025992238674935525323:ℚ)/147865600000000000000000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2307:ℚ)/3200),((4633:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3124687499:ℚ)/5000000000),((6369479823:ℚ)/10000000000),((10846062497:ℚ)/11582500000),(1:ℚ),((1905827251:ℚ)/2000000000),((1907725537:ℚ)/2000000000),((3080928657:ℚ)/10000000000),((1210759033:ℚ)/2000000000),((-185182350674366054505870249147675507714524267688793963:ℚ)/388460563035156250000000000000000000000000000000000000),((-41229751054046492445025323:ℚ)/147865600000000000000000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4633:ℚ)/6400),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3139531249:ℚ)/5000000000),((6399196279:ℚ)/10000000000),((10890593747:ℚ)/11630000000),(1:ℚ),((9519843613:ℚ)/10000000000),((476456813:ℚ)/500000000),((622285377:ℚ)/2000000000),((5984808589:ℚ)/10000000000),((-4685055938707449398289220736547984874108429680114286297:ℚ)/9831485918750000000000000000000000000000000000000000000),((-41039654348340313894900323:ℚ)/147865600000000000000000000)⟩
theorem valid12 : Valid source25 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source25 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1163:ℚ)/1600),((4671:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3154374999:ℚ)/5000000000),((6428912499:ℚ)/10000000000),((10935124997:ℚ)/11677500000),(1:ℚ),((148605427:ℚ)/156250000),((4759921809:ℚ)/5000000000),((98156347:ℚ)/312500000),((2957558457:ℚ)/5000000000),((-385825027440463544351974213032508255238542982181109:ℚ)/809931784558296203613281250000000000000000000000000),((-40849735859820835861150323:ℚ)/147865600000000000000000000)⟩
theorem valid13 : Valid source25 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((4671:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4671:ℚ)/6400),((469:ℚ)/640),((15:ℚ)/16),(1:ℚ),((3169218749:ℚ)/5000000000),((3229314243:ℚ)/5000000000),((1568522321:ℚ)/1675000000),(1:ℚ),((9501845013:ℚ)/10000000000),((9510747333:ℚ)/10000000000),((792422551:ℚ)/2500000000),((2922347287:ℚ)/5000000000),((-13986726114583622852550066199819555144598790179794379:ℚ)/29371386718750000000000000000000000000000000000000000),((-40659995565539103207775323:ℚ)/147865600000000000000000000)⟩
theorem valid14 : Valid source25 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source25 nn0 nn1 Qcell ((4671:ℚ)/6400) ((469:ℚ)/640) :=
  cell_of_packet source25 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3184062499:ℚ)/5000000000),((3244172121:ℚ)/5000000000),((11024187497:ℚ)/11772500000),(1:ℚ),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((5773514489:ℚ)/10000000000),((-285549741110512076793277377731243547540153594956883499:ℚ)/599842445019531250000000000000000000000000000000000000),((-40470433450195812510775323:ℚ)/147865600000000000000000000)⟩
theorem valid15 : Valid source25 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source25 nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3198906249:ℚ)/5000000000),((6518059771:ℚ)/10000000000),((11068718747:ℚ)/11820000000),(1:ℚ),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((570154793:ℚ)/1000000000),((-409309655513432569790534178498324060251671794024318211:ℚ)/860104462500000000000000000000000000000000000000000000),((-40281049483192356922150323:ℚ)/147865600000000000000000000)⟩
theorem valid16 : Valid source25 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source25 nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3213749999:ℚ)/5000000000),((1636943769:ℚ)/2500000000),((11113249997:ℚ)/11867500000),(1:ℚ),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((2814382191:ℚ)/5000000000),((-4969560167554934671839713262608870714318589246686224063:ℚ)/10446185617480468750000000000000000000000000000000000000),((-40091843641579781305900323:ℚ)/147865600000000000000000000)⟩
theorem valid17 : Valid source25 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3228593749:ℚ)/5000000000),((3288745079:ℚ)/5000000000),((11157781247:ℚ)/11915000000),(1:ℚ),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((5555131379:ℚ)/10000000000),((-5027880816770817482153446722708361152040202433716098397:ℚ)/10572121786718750000000000000000000000000000000000000000),((-39902815917708433950025323:ℚ)/147865600000000000000000000)⟩
theorem valid18 : Valid source25 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source25 nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((2383:ℚ)/3200),((957:ℚ)/1280),((15:ℚ)/16),(1:ℚ),((3243437499:ℚ)/5000000000),((6607205021:ℚ)/10000000000),((11202312497:ℚ)/11962500000),(1:ℚ),((75681297:ℚ)/80000000),((2367032267:ℚ)/2500000000),((1650403157:ℚ)/5000000000),((685076791:ℚ)/1250000000),((-325547528408678325958854495476548293446430473975267:ℚ)/684740228906250000000000000000000000000000000000000),((-39713966280979708006525323:ℚ)/147865600000000000000000000)⟩
theorem valid19 : Valid source25 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source25 nn0 nn1 Qcell ((2383:ℚ)/3200) ((957:ℚ)/1280) :=
  cell_of_packet source25 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((957:ℚ)/1280),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3258281249:ℚ)/5000000000),((1659229917:ℚ)/2500000000),((11246843747:ℚ)/12010000000),(1:ℚ),((4726187811:ℚ)/5000000000),((946016213:ℚ)/1000000000),((831186567:ℚ)/2500000000),((1351294077:ℚ)/2500000000),((-1286490108548544339033489112270990434622735137012148073:ℚ)/2706755626562500000000000000000000000000000000000000000),((-39525294708444648339400323:ℚ)/147865600000000000000000000)⟩
theorem valid20 : Valid source25 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source25 nn0 nn1 Qcell ((957:ℚ)/1280) ((1201:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((1201:ℚ)/1600),((4823:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3273124999:ℚ)/5000000000),((66666341:ℚ)/100000000),((1613053571:ℚ)/1722500000),(1:ℚ),((9444767421:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1673989387:ℚ)/5000000000),((1332194461:ℚ)/2500000000),((-15177038052887942119944969604873529755208953027172681:ℚ)/31941676660156250000000000000000000000000000000000000),((-39336801192453603236650323:ℚ)/147865600000000000000000000)⟩
theorem valid21 : Valid source25 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source25 nn0 nn1 Qcell ((1201:ℚ)/1600) ((4823:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((4823:ℚ)/6400),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3287968749:ℚ)/5000000000),((41852177:ℚ)/62500000),((11335906247:ℚ)/12105000000),(1:ℚ),((4718667711:ℚ)/5000000000),((4722383713:ℚ)/5000000000),((674104879:ℚ)/2000000000),((1312844163:ℚ)/2500000000),((-1316493329163054831370985529483793268260435827877321973:ℚ)/2771496965039062500000000000000000000000000000000000000),((-39148485710057617562275323:ℚ)/147865600000000000000000000)⟩
theorem valid22 : Valid source25 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source25 nn0 nn1 Qcell ((4823:ℚ)/6400) ((2421:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3302812499:ℚ)/5000000000),((844472017:ℚ)/1250000000),((11380437497:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((5172927353:ℚ)/10000000000),((-5334422240203405589919902120619821770881586769571724763:ℚ)/11349050000000000000000000000000000000000000000000000000),((-38733047979019452020275323:ℚ)/147865600000000000000000000)⟩
theorem valid23 : Valid source25 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source25 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source25 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3332499999:ℚ)/5000000000),((1363040627:ℚ)/2000000000),((11469499997:ℚ)/12295000000),(1:ℚ),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((2506342717:ℚ)/5000000000),((-341100887278924878158861045600510039312232212559024367:ℚ)/726015067333984375000000000000000000000000000000000000),((-38357310096720080085400323:ℚ)/147865600000000000000000000)⟩
theorem valid24 : Valid source25 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3362187499:ℚ)/5000000000),((1374925867:ℚ)/2000000000),((11558562497:ℚ)/12390000000),(1:ℚ),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((969522703:ℚ)/2000000000),((-620309703059526218254938581492864970690707863758191363:ℚ)/1320843693750000000000000000000000000000000000000000000),((-37982283973968011976025323:ℚ)/147865600000000000000000000)⟩
theorem valid25 : Valid source25 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source25 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3391874999:ℚ)/5000000000),((6993479413:ℚ)/10000000000),((11647624997:ℚ)/12580000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2338598523:ℚ)/5000000000),((-1431710460522025670167175422956304613711772317449607687:ℚ)/3110727362500000000000000000000000000000000000000000000),((-37153391528615150668150323:ℚ)/147865600000000000000000000)⟩
theorem valid26 : Valid source25 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source25 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((3451249999:ℚ)/5000000000),((1446234151:ℚ)/2000000000),((11825749997:ℚ)/12960000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((539720807:ℚ)/1250000000),((-669307673863815586463133319159187849574289613407151687:ℚ)/1511654400000000000000000000000000000000000000000000000),((-35497791004366375432900323:ℚ)/147865600000000000000000000)⟩
theorem valid27 : Valid source25 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source25 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((81:ℚ)/100),((343:ℚ)/400),((15:ℚ)/16),(1:ℚ),((3569999999:ℚ)/5000000000),((7706521607:ℚ)/10000000000),((12181999997:ℚ)/13720000000),(1:ℚ),((57977633:ℚ)/62500000),((2332870371:ℚ)/2500000000),((1913736159:ℚ)/5000000000),((3497054173:ℚ)/10000000000),((-259849427893496040311403586426794394694513503275007:ℚ)/630525109375000000000000000000000000000000000000000),((-33010154422641693780400323:ℚ)/147865600000000000000000000)⟩
theorem valid28 : Valid source25 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((343:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨((343:ℚ)/400),((181:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3807499999:ℚ)/5000000000),((1022729449:ℚ)/1250000000),((12894499997:ℚ)/14480000000),(1:ℚ),((9252071821:ℚ)/10000000000),((1855284257:ℚ)/2000000000),((1946075537:ℚ)/5000000000),(0:ℚ),((-7873550980403901874383531868523240325133683153510956983:ℚ)/18975171200000000000000000000000000000000000000000000000),((-233301537:ℚ)/1024000000)⟩
theorem valid29 : Valid source25 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source25 nn0 nn1 Qcell ((343:ℚ)/400) ((181:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet29 valid29
def packet30 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((15:ℚ)/16),(1:ℚ),((4044999999:ℚ)/5000000000),((9132374001:ℚ)/10000000000),((13606999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-2357051082340680674413325858010774121512973205672510463:ℚ)/6400000000000000000000000000000000000000000000000000000),((-233301537:ℚ)/1024000000)⟩
theorem valid30 : Valid source25 packet30 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf30 :
    CellBound source25 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet30 valid30
def packet31 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4519999999:ℚ)/5000000000),((12933785961:ℚ)/10000000000),((15031999997:ℚ)/22080000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-168750646822918095195040914103510463:ℚ)/897048576000000000000000000000000000),((-233301537:ℚ)/1024000000)⟩
theorem valid31 : Valid source25 packet31 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf31 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet31 valid31
private theorem node0_2 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((4557:ℚ)/6400) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((4557:ℚ)/6400) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((4557:ℚ)/6400) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source25 nn0 nn1 Qcell ((4557:ℚ)/6400) ((919:ℚ)/1280) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source25 nn0 nn1 Qcell ((919:ℚ)/1280) ((4633:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source25 nn0 nn1 Qcell ((4557:ℚ)/6400) ((4633:ℚ)/6400) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source25 nn0 nn1 Qcell ((4633:ℚ)/6400) ((4671:ℚ)/6400) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source25 nn0 nn1 Qcell ((4671:ℚ)/6400) ((4709:ℚ)/6400) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source25 nn0 nn1 Qcell ((4633:ℚ)/6400) ((4709:ℚ)/6400) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source25 nn0 nn1 Qcell ((4557:ℚ)/6400) ((4709:ℚ)/6400) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((4709:ℚ)/6400) :=
  cell_join node0_8 node8_16
private theorem node16_18 :
    CellBound source25 nn0 nn1 Qcell ((4709:ℚ)/6400) ((4747:ℚ)/6400) :=
  cell_join leaf16 leaf17
private theorem node18_20 :
    CellBound source25 nn0 nn1 Qcell ((4747:ℚ)/6400) ((957:ℚ)/1280) :=
  cell_join leaf18 leaf19
private theorem node16_20 :
    CellBound source25 nn0 nn1 Qcell ((4709:ℚ)/6400) ((957:ℚ)/1280) :=
  cell_join node16_18 node18_20
private theorem node20_22 :
    CellBound source25 nn0 nn1 Qcell ((957:ℚ)/1280) ((4823:ℚ)/6400) :=
  cell_join leaf20 leaf21
private theorem node22_24 :
    CellBound source25 nn0 nn1 Qcell ((4823:ℚ)/6400) ((61:ℚ)/80) :=
  cell_join leaf22 leaf23
private theorem node20_24 :
    CellBound source25 nn0 nn1 Qcell ((957:ℚ)/1280) ((61:ℚ)/80) :=
  cell_join node20_22 node22_24
private theorem node16_24 :
    CellBound source25 nn0 nn1 Qcell ((4709:ℚ)/6400) ((61:ℚ)/80) :=
  cell_join node16_20 node20_24
private theorem node24_26 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf24 leaf25
private theorem node26_28 :
    CellBound source25 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf26 leaf27
private theorem node24_28 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join node24_26 node26_28
private theorem node28_30 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_join leaf28 leaf29
private theorem node30_32 :
    CellBound source25 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf30 leaf31
private theorem node28_32 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join node28_30 node30_32
private theorem node24_32 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node24_28 node28_32
private theorem node16_32 :
    CellBound source25 nn0 nn1 Qcell ((4709:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node16_24 node24_32
private theorem node0_32 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_16 node16_32
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_32
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29,packet30,packet31]
theorem packet_count : packets.length = 32 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC32
#check @N11Formalization.C450Source25GroupedC32.bound
#print axioms N11Formalization.C450Source25GroupedC32.valid0
#print axioms N11Formalization.C450Source25GroupedC32.valid1
#print axioms N11Formalization.C450Source25GroupedC32.valid2
#print axioms N11Formalization.C450Source25GroupedC32.valid3
#print axioms N11Formalization.C450Source25GroupedC32.valid4
#print axioms N11Formalization.C450Source25GroupedC32.valid5
#print axioms N11Formalization.C450Source25GroupedC32.valid6
#print axioms N11Formalization.C450Source25GroupedC32.valid7
#print axioms N11Formalization.C450Source25GroupedC32.valid8
#print axioms N11Formalization.C450Source25GroupedC32.valid9
#print axioms N11Formalization.C450Source25GroupedC32.valid10
#print axioms N11Formalization.C450Source25GroupedC32.valid11
#print axioms N11Formalization.C450Source25GroupedC32.valid12
#print axioms N11Formalization.C450Source25GroupedC32.valid13
#print axioms N11Formalization.C450Source25GroupedC32.valid14
#print axioms N11Formalization.C450Source25GroupedC32.valid15
#print axioms N11Formalization.C450Source25GroupedC32.valid16
#print axioms N11Formalization.C450Source25GroupedC32.valid17
#print axioms N11Formalization.C450Source25GroupedC32.valid18
#print axioms N11Formalization.C450Source25GroupedC32.valid19
#print axioms N11Formalization.C450Source25GroupedC32.valid20
#print axioms N11Formalization.C450Source25GroupedC32.valid21
#print axioms N11Formalization.C450Source25GroupedC32.valid22
#print axioms N11Formalization.C450Source25GroupedC32.valid23
#print axioms N11Formalization.C450Source25GroupedC32.valid24
#print axioms N11Formalization.C450Source25GroupedC32.valid25
#print axioms N11Formalization.C450Source25GroupedC32.valid26
#print axioms N11Formalization.C450Source25GroupedC32.valid27
#print axioms N11Formalization.C450Source25GroupedC32.valid28
#print axioms N11Formalization.C450Source25GroupedC32.valid29
#print axioms N11Formalization.C450Source25GroupedC32.valid30
#print axioms N11Formalization.C450Source25GroupedC32.valid31
#print axioms N11Formalization.C450Source25GroupedC32.bound
#print axioms N11Formalization.C450Source25GroupedC32.endpoint_checks
