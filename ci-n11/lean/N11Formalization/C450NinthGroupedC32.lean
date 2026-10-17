import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((2939999999:ℚ)/5000000000),((3205894411:ℚ)/5000000000),((9267999997:ℚ)/10680000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6861606557:ℚ)/10000000000),((-67954101783543310184799445047435176124646016710373261:ℚ)/1903416300000000000000000000000000000000000000000000000),((-650839964760136134553157:ℚ)/3610000000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3177499999:ℚ)/5000000000),((332465663:ℚ)/500000000),((126335443:ℚ)/140000000),(1:ℚ),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1451269707:ℚ)/2500000000),((-32204969012516851107152479984875199422113085593:ℚ)/803906250000000000000000000000000000000000000000),((-6450754299181740672173:ℚ)/36100000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((15:ℚ)/16),(1:ℚ),((3296249999:ℚ)/5000000000),((6768074859:ℚ)/10000000000),((10336749997:ℚ)/11250000000),(1:ℚ),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2083097:ℚ)/4000000),((-4398058535510660485241381561182736190550873544133623:ℚ)/104284286499023437500000000000000000000000000000000000),((-7706172192649353876780431:ℚ)/43320000000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3355624999:ℚ)/5000000000),((6886836073:ℚ)/10000000000),((955897727:ℚ)/1040000000),(1:ℚ),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((976908773:ℚ)/2000000000),((-296263196382512893603144880024984328218931470471831:ℚ)/7030400000000000000000000000000000000000000000000000),((-2557114015923082287492093:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3414999999:ℚ)/5000000000),((3473108271:ℚ)/5000000000),((10692999997:ℚ)/11535000000),(1:ℚ),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((4540360963:ℚ)/10000000000),((-48517721672212069696966917030778708079217169351487:ℚ)/1124123697784423828125000000000000000000000000000000),((-1913472632952059886037991:ℚ)/10830000000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3444687499:ℚ)/5000000000),((7005596921:ℚ)/10000000000),((10782062497:ℚ)/11630000000),(1:ℚ),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((4358850683:ℚ)/10000000000),((-424086344279486266068606904656806982406603751259144169:ℚ)/9831485918750000000000000000000000000000000000000000000),((-2545471573242772125949597:ℚ)/14440000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((15:ℚ)/16),(1:ℚ),((3474374999:ℚ)/5000000000),((7064977213:ℚ)/10000000000),((10871124997:ℚ)/11725000000),(1:ℚ),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((208498643:ℚ)/500000000),((-1302977152131257363011244980845117629334301798798694207:ℚ)/30223156933593750000000000000000000000000000000000000000),((-2539638203585106435274773:ℚ)/14440000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((7008124997:ℚ)/10000000000),((356217871:ℚ)/500000000),((21920374991:ℚ)/23640000000),(1:ℚ),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3972673183:ℚ)/10000000000),((-296491838345549094539406704082966245909248604838232469:ℚ)/6880835700000000000000000000000000000000000000000000000),((-17547068800566716677:ℚ)/100000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3533749999:ℚ)/5000000000),((1788511873:ℚ)/2500000000),((11049249997:ℚ)/11867500000),(1:ℚ),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((470703041:ℚ)/1250000000),((-455265233965690580536908337029954795975183711784731301:ℚ)/10446185617480468750000000000000000000000000000000000000),((-158179560200752107307693:ℚ)/902500000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3548593749:ℚ)/5000000000),((7183737543:ℚ)/10000000000),((11093781247:ℚ)/11915000000),(1:ℚ),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((731585701:ℚ)/2000000000),((-1381850691591134913447732340217204602982598232806341357:ℚ)/31716365360156250000000000000000000000000000000000000000),((-7583841500487576222547799:ℚ)/43320000000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((957:ℚ)/1280),((15:ℚ)/16),(1:ℚ),((3563437499:ℚ)/5000000000),((288537103:ℚ)/400000000),((11138312497:ℚ)/11962500000),(1:ℚ),((75681297:ℚ)/80000000),((2367032267:ℚ)/2500000000),((1650403157:ℚ)/5000000000),((88677889:ℚ)/250000000),((-89474461047964681423221111839066598833510021919827:ℚ)/2054220686718750000000000000000000000000000000000000),((-4040030952736505043853:ℚ)/23104000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((2383:ℚ)/3200) ((957:ℚ)/1280) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((957:ℚ)/1280),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3578281249:ℚ)/5000000000),((3621558793:ℚ)/5000000000),((11182843747:ℚ)/12010000000),(1:ℚ),((4726187811:ℚ)/5000000000),((946016213:ℚ)/1000000000),((831186567:ℚ)/2500000000),((3432883141:ℚ)/10000000000),((-353589913708291329788776855695991760395613365925334713:ℚ)/8120266879687500000000000000000000000000000000000000000),((-630522374826681592495933:ℚ)/3610000000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((957:ℚ)/1280) ((1201:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3593124999:ℚ)/5000000000),((146049951:ℚ)/200000000),((11227374997:ℚ)/12105000000),(1:ℚ),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((82871931:ℚ)/250000000),((-357770601780462848138045903211427411851807999286641863:ℚ)/8314490895117187500000000000000000000000000000000000000),((-3019468478602023818951:ℚ)/17328000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3622812499:ℚ)/5000000000),((1840469359:ℚ)/2500000000),((11316437497:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1532893187:ℚ)/5000000000),((-1464443416167619314853673688784546238859293986542470603:ℚ)/34047150000000000000000000000000000000000000000000000000),((-156896866584215171110477:ℚ)/902500000000000000000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((7304999997:ℚ)/10000000000),((7421257247:ℚ)/10000000000),((22810999991:ℚ)/24590000000),(1:ℚ),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((139766829:ℚ)/500000000),((-249724831219434569705673405574069385279602108687812343:ℚ)/5808120538671875000000000000000000000000000000000000000),((-2504467898578569194812653:ℚ)/14440000000000000000000000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3682187499:ℚ)/5000000000),((935079623:ℚ)/1250000000),((11494562497:ℚ)/12390000000),(1:ℚ),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((1248295403:ℚ)/5000000000),((-510934835600629400410140943045230927456958381560875609:ℚ)/11887593243750000000000000000000000000000000000000000000),((-108144816126782861013:ℚ)/625000000000000000000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3711874999:ℚ)/5000000000),((7599396243:ℚ)/10000000000),((11583624997:ℚ)/12580000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2157822223:ℚ)/10000000000),((-392171339200120958141832972622923581863970561672977847:ℚ)/9332182087500000000000000000000000000000000000000000000),((-7460320192792266445595999:ℚ)/43320000000000000000000000)⟩
theorem valid16 : Valid ninth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound ninth nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((3771249999:ℚ)/5000000000),((7836913947:ℚ)/10000000000),((11761749997:ℚ)/12960000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1230881737:ℚ)/10000000000),((-182500556149748839002765513402300258338301602176441847:ℚ)/4534963200000000000000000000000000000000000000000000000),((-2755361:ℚ)/16000000)⟩
theorem valid17 : Valid ninth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound ninth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((15:ℚ)/16),(1:ℚ),((3889999999:ℚ)/5000000000),((1217128163:ℚ)/1250000000),((12117999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-110514979267604431985063604559878654242455536414637223:ℚ)/4800000000000000000000000000000000000000000000000000000),((-2755361:ℚ)/16000000)⟩
theorem valid18 : Valid ninth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4839999999:ℚ)/5000000000),((6768578011:ℚ)/5000000000),((14967999997:ℚ)/22080000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-39020668322386696796694690615832303:ℚ)/2691145728000000000000000000000000000),((-2755361:ℚ)/16000000)⟩
theorem valid19 : Valid ninth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet19 valid19
private theorem node0_2 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((2307:ℚ)/3200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((2383:ℚ)/3200) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((2383:ℚ)/3200) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound ninth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound ninth nn0 nn1 Qcell ((2421:ℚ)/3200) ((2459:ℚ)/3200) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2459:ℚ)/3200) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound ninth nn0 nn1 Qcell ((2383:ℚ)/3200) ((2459:ℚ)/3200) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound ninth nn0 nn1 Qcell ((2459:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound ninth nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound ninth nn0 nn1 Qcell ((2459:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound ninth nn0 nn1 Qcell ((2383:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC32
#check @N11Formalization.C450NinthGroupedC32.bound
#print axioms N11Formalization.C450NinthGroupedC32.valid0
#print axioms N11Formalization.C450NinthGroupedC32.valid1
#print axioms N11Formalization.C450NinthGroupedC32.valid2
#print axioms N11Formalization.C450NinthGroupedC32.valid3
#print axioms N11Formalization.C450NinthGroupedC32.valid4
#print axioms N11Formalization.C450NinthGroupedC32.valid5
#print axioms N11Formalization.C450NinthGroupedC32.valid6
#print axioms N11Formalization.C450NinthGroupedC32.valid7
#print axioms N11Formalization.C450NinthGroupedC32.valid8
#print axioms N11Formalization.C450NinthGroupedC32.valid9
#print axioms N11Formalization.C450NinthGroupedC32.valid10
#print axioms N11Formalization.C450NinthGroupedC32.valid11
#print axioms N11Formalization.C450NinthGroupedC32.valid12
#print axioms N11Formalization.C450NinthGroupedC32.valid13
#print axioms N11Formalization.C450NinthGroupedC32.valid14
#print axioms N11Formalization.C450NinthGroupedC32.valid15
#print axioms N11Formalization.C450NinthGroupedC32.valid16
#print axioms N11Formalization.C450NinthGroupedC32.valid17
#print axioms N11Formalization.C450NinthGroupedC32.valid18
#print axioms N11Formalization.C450NinthGroupedC32.valid19
#print axioms N11Formalization.C450NinthGroupedC32.bound
#print axioms N11Formalization.C450NinthGroupedC32.endpoint_checks
