import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((2979999999:ℚ)/5000000000),((1297427433:ℚ)/2000000000),((9259999997:ℚ)/10680000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3346867773:ℚ)/5000000000),((-17229314478902426916386198027887319130959310781182173:ℚ)/951708150000000000000000000000000000000000000000000000),((-31555554101100612219283:ℚ)/216600000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3217499999:ℚ)/5000000000),((210145301:ℚ)/312500000),((9972499997:ℚ)/11060000000),(1:ℚ),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2805121939:ℚ)/5000000000),((-4020982957051127889667598936799511121343903281255111:ℚ)/198178566796875000000000000000000000000000000000000000),((-353610022332579267:ℚ)/2441406250000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((15:ℚ)/16),(1:ℚ),((3336249999:ℚ)/5000000000),((136868111:ℚ)/200000000),((10328749997:ℚ)/11250000000),(1:ℚ),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((624013827:ℚ)/1250000000),((-1113190279837793485573594943489119553544130127249639:ℚ)/52142143249511718750000000000000000000000000000000000),((-104266257775769014929:ℚ)/722000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3395624999:ℚ)/5000000000),((6962161271:ℚ)/10000000000),((10506874997:ℚ)/11440000000),(1:ℚ),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4655261017:ℚ)/10000000000),((-99813888050651913427475331400991102690634427778745573:ℚ)/4678731200000000000000000000000000000000000000000000000),((-259895120867300563877809:ℚ)/1805000000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3454999999:ℚ)/5000000000),((7021539061:ℚ)/10000000000),((10684999997:ℚ)/11535000000),(1:ℚ),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2147062241:ℚ)/5000000000),((-12278235227453604342748045595185866328636403804591:ℚ)/562061848892211914062500000000000000000000000000000),((-259508967530307000261529:ℚ)/1805000000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3484687499:ℚ)/5000000000),((1416183361:ℚ)/2000000000),((10774062497:ℚ)/11630000000),(1:ℚ),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((4102452759:ℚ)/10000000000),((-107325626826511126121025701226523905647570764808045817:ℚ)/4915742959375000000000000000000000000000000000000000000),((-10364888792855581216929:ℚ)/72200000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((15:ℚ)/16),(1:ℚ),((3514374999:ℚ)/5000000000),((1428058901:ℚ)/2000000000),((10863124997:ℚ)/11725000000),(1:ℚ),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3901933689:ℚ)/10000000000),((-329760868075130747552204546835264114721388270936805551:ℚ)/15111578466796875000000000000000000000000000000000000000),((-10349395109154939855449:ℚ)/72200000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3544062499:ℚ)/5000000000),((3584991669:ℚ)/5000000000),((10952187497:ℚ)/11772500000),(1:ℚ),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((922780461:ℚ)/2500000000),((-1168152385658429647925664713719446771840451101252251:ℚ)/52927274560546875000000000000000000000000000000000000),((-193905737844334369143067:ℚ)/1353750000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3558906249:ℚ)/5000000000),((7199672161:ℚ)/10000000000),((10996718747:ℚ)/11820000000),(1:ℚ),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((447661301:ℚ)/1250000000),((-9488814901261945813821138596868448649631283194426721:ℚ)/430052231250000000000000000000000000000000000000000000),((-258346941254080883263329:ℚ)/1805000000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3573749999:ℚ)/5000000000),((7229360973:ℚ)/10000000000),((11041249997:ℚ)/11867500000),(1:ℚ),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((3468136759:ℚ)/10000000000),((-115210645421702706250483387374501984668709211434475893:ℚ)/5223092808740234375000000000000000000000000000000000000),((-774458250361416854297563:ℚ)/5415000000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3588593749:ℚ)/5000000000),((290361991:ℚ)/400000000),((11085781247:ℚ)/11915000000),(1:ℚ),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((3351323889:ℚ)/10000000000),((-349700006426151944922452985566562675519664685462525501:ℚ)/15858182680078125000000000000000000000000000000000000000),((-412733456616379009169:ℚ)/2888000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2383:ℚ)/3200),((957:ℚ)/1280),((15:ℚ)/16),(1:ℚ),((3603437499:ℚ)/5000000000),((7288738567:ℚ)/10000000000),((11130312497:ℚ)/11962500000),(1:ℚ),((75681297:ℚ)/80000000),((2367032267:ℚ)/2500000000),((1650403157:ℚ)/5000000000),((3230454339:ℚ)/10000000000),((-22643309744666779102143636328296691194586288126211:ℚ)/1027110343359375000000000000000000000000000000000000),((-257763922048524896495761:ℚ)/1805000000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((2383:ℚ)/3200) ((957:ℚ)/1280) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((957:ℚ)/1280),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3618281249:ℚ)/5000000000),((1829606837:ℚ)/2500000000),((11174843747:ℚ)/12010000000),(1:ℚ),((4726187811:ℚ)/5000000000),((946016213:ℚ)/1000000000),((831186567:ℚ)/2500000000),((1552526929:ℚ)/5000000000),((-89484307381417919825886048717348524277516934422392009:ℚ)/4060133439843750000000000000000000000000000000000000000),((-16098080319815310599681:ℚ)/112812500000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((957:ℚ)/1280) ((1201:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3633124999:ℚ)/5000000000),((92222561:ℚ)/125000000),((11219374997:ℚ)/12105000000),(1:ℚ),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((2974548887:ℚ)/10000000000),((-90555669582516383770176817069713520516414191172491959:ℚ)/4157245447558593750000000000000000000000000000000000000),((-111313870087749739:ℚ)/781250000000000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3662812499:ℚ)/5000000000),((7437182373:ℚ)/10000000000),((11308437497:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1347614843:ℚ)/5000000000),((-370676290751330387528527642601676696751255144071990779:ℚ)/17023575000000000000000000000000000000000000000000000000),((-770367754123163773984363:ℚ)/5415000000000000000000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((7384999997:ℚ)/10000000000),((1888984311:ℚ)/2500000000),((22794999991:ℚ)/24780000000),(1:ℚ),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1192138247:ℚ)/5000000000),((-1012112251098329887201721371318349996391142771325782399:ℚ)/47550372975000000000000000000000000000000000000000000000),((-48001282496823104510587:ℚ)/338437500000000000000000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3751874999:ℚ)/5000000000),((59958531:ℚ)/78125000),((11575624997:ℚ)/12580000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1593191521:ℚ)/10000000000),((-99297923538812118751713187905444193659084192322620071:ℚ)/4666091043750000000000000000000000000000000000000000000),((-1133367:ℚ)/8000000)⟩
theorem valid16 : Valid seventh packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound seventh nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((3811249999:ℚ)/5000000000),((7912201:ℚ)/10000000),((11753749997:ℚ)/12960000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-46234097428276308889899894304685898584735593878372071:ℚ)/2267481600000000000000000000000000000000000000000000000),((-1133367:ℚ)/8000000)⟩
theorem valid17 : Valid seventh packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound seventh nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((15:ℚ)/16),(1:ℚ),((3929999999:ℚ)/5000000000),((2453064453:ℚ)/2500000000),((12109999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-28213049860962832844088047628318908971609252275724439:ℚ)/2400000000000000000000000000000000000000000000000000000),((-1133367:ℚ)/8000000)⟩
theorem valid18 : Valid seventh packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4879999999:ℚ)/5000000000),((13612324503:ℚ)/10000000000),((14959999997:ℚ)/22080000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-10068210625450444884268748559958879:ℚ)/1345572864000000000000000000000000000),((-1133367:ℚ)/8000000)⟩
theorem valid19 : Valid seventh packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet19 valid19
private theorem node0_2 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((2307:ℚ)/3200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound seventh nn0 nn1 Qcell ((4709:ℚ)/6400) ((4747:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((4747:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((4747:ℚ)/6400) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((4747:ℚ)/6400) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound seventh nn0 nn1 Qcell ((4747:ℚ)/6400) ((957:ℚ)/1280) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound seventh nn0 nn1 Qcell ((957:ℚ)/1280) ((61:ℚ)/80) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound seventh nn0 nn1 Qcell ((4747:ℚ)/6400) ((61:ℚ)/80) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound seventh nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound seventh nn0 nn1 Qcell ((4747:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC32
#check @N11Formalization.C450SeventhGroupedC32.bound
#print axioms N11Formalization.C450SeventhGroupedC32.valid0
#print axioms N11Formalization.C450SeventhGroupedC32.valid1
#print axioms N11Formalization.C450SeventhGroupedC32.valid2
#print axioms N11Formalization.C450SeventhGroupedC32.valid3
#print axioms N11Formalization.C450SeventhGroupedC32.valid4
#print axioms N11Formalization.C450SeventhGroupedC32.valid5
#print axioms N11Formalization.C450SeventhGroupedC32.valid6
#print axioms N11Formalization.C450SeventhGroupedC32.valid7
#print axioms N11Formalization.C450SeventhGroupedC32.valid8
#print axioms N11Formalization.C450SeventhGroupedC32.valid9
#print axioms N11Formalization.C450SeventhGroupedC32.valid10
#print axioms N11Formalization.C450SeventhGroupedC32.valid11
#print axioms N11Formalization.C450SeventhGroupedC32.valid12
#print axioms N11Formalization.C450SeventhGroupedC32.valid13
#print axioms N11Formalization.C450SeventhGroupedC32.valid14
#print axioms N11Formalization.C450SeventhGroupedC32.valid15
#print axioms N11Formalization.C450SeventhGroupedC32.valid16
#print axioms N11Formalization.C450SeventhGroupedC32.valid17
#print axioms N11Formalization.C450SeventhGroupedC32.valid18
#print axioms N11Formalization.C450SeventhGroupedC32.valid19
#print axioms N11Formalization.C450SeventhGroupedC32.bound
#print axioms N11Formalization.C450SeventhGroupedC32.endpoint_checks
