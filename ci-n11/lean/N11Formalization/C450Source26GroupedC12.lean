import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((1592481647:ℚ)/2500000000),((6679529333:ℚ)/10000000000),((-3607529333:ℚ)/19840000000),((-5752249:ℚ)/62500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2884584951:ℚ)/5000000000),((28482162934080519308253446162541091292207033718053:ℚ)/141906738281250000000000000000000000000000000000000),((-25255106259544273006377:ℚ)/288800000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((3305019867:ℚ)/5000000000),((6799569473:ℚ)/10000000000),((-3727569473:ℚ)/20600000000),((-1305019867:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1032233789:ℚ)/2000000000),((71401905045511390075369421959920185267998275189650232109:ℚ)/362838827047729492187500000000000000000000000000000000000),((-348598763803903134582851:ℚ)/3465600000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((6730024193:ℚ)/10000000000),((1383912597:ℚ)/2000000000),((-769512597:ℚ)/4196000000),((-2730024193:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((603954777:ℚ)/1250000000),((6127766732782296127208811431280518456695130572752361658857:ℚ)/31198182792187500000000000000000000000000000000000000000000),((-495323638109017984920297:ℚ)/4620800000000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((6849964067:ℚ)/10000000000),((1759878091:ℚ)/2500000000),((-991878091:ℚ)/5340000000),((-2849964067:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2240048141:ℚ)/5000000000),((6566714522229004823490328217486840315051733713073398897329:ℚ)/33488827080175781250000000000000000000000000000000000000000),((-525960927241330854636017:ℚ)/4620800000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((6969861739:ℚ)/10000000000),((1419894247:ℚ)/2000000000),((-805494247:ℚ)/4348000000),((-989953913:ℚ)/9137500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4100846661:ℚ)/10000000000),((251909718544745351056191532853511428854082417176315041791:ℚ)/1295781395010375976562500000000000000000000000000000000000),((-556710693992900360297313:ℚ)/4620800000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((878724431:ℚ)/1250000000),((715941993:ℚ)/1000000000),((-136247331:ℚ)/731000000),((-378724431:ℚ)/3456250000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3898315613:ℚ)/10000000000),((572648745914260928168990003140162098128957869865679701:ℚ)/2947357835459709167480468750000000000000000000000000000),((-8939498370819014014233:ℚ)/72200000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((3544859713:ℚ)/5000000000),((3609679357:ℚ)/5000000000),((-2073679357:ℚ)/11060000000),((-1544859713:ℚ)/13943750000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((18426513:ℚ)/50000000),((113721210421312232961143069434729875110945870985745412081:ℚ)/585630826208400726318359375000000000000000000000000000000),((-146893345059191943807657:ℚ)/1155200000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((285985357:ℚ)/400000000),((7279287843:ℚ)/10000000000),((-4207287843:ℚ)/22310000000),((-13998373:ℚ)/125000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3459866707:ℚ)/10000000000),((61942622159780783890320121859251717000406113241089:ℚ)/319147109985351562500000000000000000000000000000000),((-964875516250817378897:ℚ)/7393280000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((720953919:ℚ)/1000000000),((7399118113:ℚ)/10000000000),((-4327118113:ℚ)/22500000000),((-2244433:ℚ)/20000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3219393537:ℚ)/10000000000),((87902687243052889168000104757813559275410440617:ℚ)/450000000000000000000000000000000000000000000000),((-18556481905501347435899:ℚ)/138624000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((1465864591:ℚ)/2000000000),((7638673117:ℚ)/10000000000),((-4566673117:ℚ)/22880000000),((-665864591:ℚ)/5910000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1338447633:ℚ)/5000000000),((1013469709215787196135808340261986838693091369490469873:ℚ)/5124789089062500000000000000000000000000000000000000000),((-25985565093270391278793:ℚ)/184832000000000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((3784394773:ℚ)/5000000000),((7878098541:ℚ)/10000000000),((-1602032847:ℚ)/7880000000),((-1784394773:ℚ)/15250000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((906581771:ℚ)/10000000000),((2585827036640684423935717542257561035277717334750784264523:ℚ)/13100172949218750000000000000000000000000000000000000000000),((-178040284086991254047137:ℚ)/1155200000000000000000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((3904066099:ℚ)/5000000000),((8356606929:ℚ)/10000000000),((-5284606929:ℚ)/24400000000),((-1904066099:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((109063781200793368185707687324790025693896577631478309997:ℚ)/540298350000000000000000000000000000000000000000000000000),((-2494273:ℚ)/16000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((1657297983:ℚ)/2000000000),((410691223:ℚ)/400000000),((-287811223:ℚ)/1036800000),((-857297983:ℚ)/8000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((58606765663723912899961595813181262928141998705452429983:ℚ)/259200000000000000000000000000000000000000000000000000000),((-2494273:ℚ)/16000000)⟩
theorem valid12 : Valid source26 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((254917657:ℚ)/250000000),((14079767569:ℚ)/10000000000),((-11007767569:ℚ)/32000000000),((-51639219:ℚ)/460000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((39489785090199161287543253173834843418598232190531:ℚ)/152087500000000000000000000000000000000000000000000),((-2494273:ℚ)/16000000)⟩
theorem valid13 : Valid source26 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source26 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((2231:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source26 nn0 nn1 Qcell ((2231:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source26 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC12
#check @N11Formalization.C450Source26GroupedC12.bound
#print axioms N11Formalization.C450Source26GroupedC12.valid0
#print axioms N11Formalization.C450Source26GroupedC12.valid1
#print axioms N11Formalization.C450Source26GroupedC12.valid2
#print axioms N11Formalization.C450Source26GroupedC12.valid3
#print axioms N11Formalization.C450Source26GroupedC12.valid4
#print axioms N11Formalization.C450Source26GroupedC12.valid5
#print axioms N11Formalization.C450Source26GroupedC12.valid6
#print axioms N11Formalization.C450Source26GroupedC12.valid7
#print axioms N11Formalization.C450Source26GroupedC12.valid8
#print axioms N11Formalization.C450Source26GroupedC12.valid9
#print axioms N11Formalization.C450Source26GroupedC12.valid10
#print axioms N11Formalization.C450Source26GroupedC12.valid11
#print axioms N11Formalization.C450Source26GroupedC12.valid12
#print axioms N11Formalization.C450Source26GroupedC12.valid13
#print axioms N11Formalization.C450Source26GroupedC12.bound
#print axioms N11Formalization.C450Source26GroupedC12.endpoint_checks
