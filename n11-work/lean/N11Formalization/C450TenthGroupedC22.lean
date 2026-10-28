import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((6056011627:ℚ)/10000000000),((3284037531:ℚ)/5000000000),((7080011627:ℚ)/21360000000),((11292112593:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((32437171:ℚ)/50000000),((2553277897385364360607243779069521458471:ℚ)/271842636672000000000000000000000000000000),((-335762125265461002595604579:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((6531652081:ℚ)/10000000000),((850726653:ℚ)/1250000000),((7555652081:ℚ)/22120000000),((970726653:ℚ)/2225000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1073293411:ℚ)/2000000000),((167610757316065544041316908912752766268611095964859593993:ℚ)/21053307121191406250000000000000000000000000000000000000000),((-343276973682720805184307611:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/16),((3:ℚ)/8),((169235981:ℚ)/250000000),((6924676263:ℚ)/10000000000),((64945327:ℚ)/187500000),((23654028789:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2359395573:ℚ)/5000000000),((1425095418160262918205984106407020415446317987263679201:ℚ)/194134106250000000000000000000000000000000000000000000000),((-216907734547166659999411:ℚ)/1848320000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((1722081383:ℚ)/2500000000),((3521767771:ℚ)/5000000000),((1978081383:ℚ)/5720000000),((4001767771:ℚ)/9375000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((872424021:ℚ)/2000000000),((762282590697655054879751750460793722755951210909298428311:ℚ)/105309104919433593750000000000000000000000000000000000000000),((-21809036532485256317928139:ℚ)/184832000000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((5:ℚ)/16),((3:ℚ)/8),((7007207289:ℚ)/10000000000),((7102963829:ℚ)/10000000000),((8031207289:ℚ)/23070000000),((24188891487:ℚ)/57200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((993948253:ℚ)/2500000000),((1203984914451499869870134090780996205761196138692320362086603:ℚ)/172926197572700000000000000000000000000000000000000000000000000),((-350839804050902191428994571:ℚ)/2957312000000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((3533323269:ℚ)/5000000000),((1432478249:ℚ)/2000000000),((4045323269:ℚ)/11630000000),((1624478249:ℚ)/3845000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3768676983:ℚ)/10000000000),((133035548733127530260159227061321151572629870727731958901:ℚ)/19221552871203781250000000000000000000000000000000000000000),((-87947135924880690032513411:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((5:ℚ)/16),((3:ℚ)/8),((1425216947:ℚ)/2000000000),((7221817811:ℚ)/10000000000),((1630016947:ℚ)/4690000000),((21105291:ℚ)/50000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3550108189:ℚ)/10000000000),((295659571589111566063350599281568388537882349122599:ℚ)/42961132812500000000000000000000000000000000000000000),((-14109521483834312440222259:ℚ)/118292480000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((3592760953:ℚ)/5000000000),((3640621773:ℚ)/5000000000),((1368253651:ℚ)/3940000000),((12361865319:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1658909823:ℚ)/5000000000),((1493422824726198511395009670298147122568533108778638052757:ℚ)/218179035981369018554687500000000000000000000000000000000000),((-88422071153708979669659659:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((5:ℚ)/16),((3:ℚ)/8),((7244958077:ℚ)/10000000000),((917583559:ℚ)/1250000000),((8268958077:ℚ)/23830000000),((1037583559:ℚ)/2462500000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((30686927:ℚ)/100000000),((10827208294559930653093673247475492516406187818646177540833:ℚ)/1589930257177624511718750000000000000000000000000000000000000),((-982380295381536145093339:ℚ)/8192000000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((730439327:ℚ)/1000000000),((3700046303:ℚ)/5000000000),((832839327:ℚ)/2402000000),((12540138909:ℚ)/29787500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((111929143:ℚ)/400000000),((100918064175406700901719274894966407840346385357456867238129:ℚ)/14891834997348546600341796875000000000000000000000000000000000),((-3555910434631006536120379:ℚ)/29573120000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((736382751:ℚ)/1000000000),((7518938577:ℚ)/10000000000),((838782751:ℚ)/2440000000),((25436815731:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1249752393:ℚ)/5000000000),((571145606941186032869103653020144310686573565755409291811:ℚ)/82556046610156250000000000000000000000000000000000000000000),((-3565435554687209582837051:ℚ)/29573120000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((3741346609:ℚ)/5000000000),((1939155453:ℚ)/2500000000),((4253346609:ℚ)/12580000000),((6537466359:ℚ)/15250000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((351851949:ℚ)/2000000000),((15758097150998765922413144312493323473626256926536356142059:ℚ)/2192455806176757812500000000000000000000000000000000000000000),((-89612711563647997023771931:ℚ)/739328000000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((3860207067:ℚ)/5000000000),((7994294289:ℚ)/10000000000),((4372207067:ℚ)/12960000000),((26862882867:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((72219398991276061386144669420717647570633546628083213884847:ℚ)/10204741112681250000000000000000000000000000000000000000000000),((-124770133:ℚ)/1024000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((7958122077:ℚ)/10000000000),((1979075787:ℚ)/2000000000),((8982122077:ℚ)/32000000000),((241230643:ℚ)/480000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((19776413255762206730219003687079271:ℚ)/1920000000000000000000000000000000000),((-124770133:ℚ)/1024000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((154053589:ℚ)/156250000),((1369665177:ℚ)/1000000000),((170053589:ℚ)/690000000),((4396995531:ℚ)/8000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1696750977894771619583:ℚ)/119025000000000000000000),((-124770133:ℚ)/1024000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound tenth nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC22
#check @N11Formalization.C450TenthGroupedC22.bound
#print axioms N11Formalization.C450TenthGroupedC22.valid0
#print axioms N11Formalization.C450TenthGroupedC22.valid1
#print axioms N11Formalization.C450TenthGroupedC22.valid2
#print axioms N11Formalization.C450TenthGroupedC22.valid3
#print axioms N11Formalization.C450TenthGroupedC22.valid4
#print axioms N11Formalization.C450TenthGroupedC22.valid5
#print axioms N11Formalization.C450TenthGroupedC22.valid6
#print axioms N11Formalization.C450TenthGroupedC22.valid7
#print axioms N11Formalization.C450TenthGroupedC22.valid8
#print axioms N11Formalization.C450TenthGroupedC22.valid9
#print axioms N11Formalization.C450TenthGroupedC22.valid10
#print axioms N11Formalization.C450TenthGroupedC22.valid11
#print axioms N11Formalization.C450TenthGroupedC22.valid12
#print axioms N11Formalization.C450TenthGroupedC22.valid13
#print axioms N11Formalization.C450TenthGroupedC22.valid14
#print axioms N11Formalization.C450TenthGroupedC22.bound
#print axioms N11Formalization.C450TenthGroupedC22.endpoint_checks
