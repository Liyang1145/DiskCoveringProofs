import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((1685715283:ℚ)/2500000000),((1739492761:ℚ)/2500000000),((-1307492761:ℚ)/2480000000),((-10691437547:ℚ)/25275000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((599394323:ℚ)/1250000000),((2884022463236726086992401041:ℚ)/9901797187500000000000000000),((20413218222642139060793:ℚ)/64000000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((6862838343:ℚ)/10000000000),((7017917263:ℚ)/10000000000),((-5289917263:ℚ)/10110000000),((-43845545087:ℚ)/102050000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((2220414659:ℚ)/5000000000),((3791632272143187923121956576889857889833:ℚ)/13160948409375000000000000000000000000000),((348245915415511425355643579:ℚ)/1108992000000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((432675597:ℚ)/625000000),((1769463199:ℚ)/2500000000),((-1337463199:ℚ)/2551250000),((-2774080373:ℚ)/6437500000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((425346053:ℚ)/1000000000),((73083475949938640881606533165513967667:ℚ)/253745730468750000000000000000000000000),((1349539691316412657917539:ℚ)/4332000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((4364231:ℚ)/6250000),((7137777939:ℚ)/10000000000),((-5409777939:ℚ)/10300000000),((-28078079:ℚ)/64968750),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((507254479:ℚ)/1250000000),((312968745984764718242309334970741:ℚ)/1086891657714843750000000000000000),((44622483596978526377:ℚ)/144400000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((3521359399:ℚ)/5000000000),((7197692983:ℚ)/10000000000),((-5469692983:ℚ)/10395000000),((-22732234591:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3853324523:ℚ)/10000000000),((8232596418228822989469146724521366306227:ℚ)/28596670987500000000000000000000000000000),((28325120848206455884329257:ℚ)/92416000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-5:ℚ)/8),((-9:ℚ)/16),((887832181:ℚ)/1250000000),((7227646803:ℚ)/10000000000),((-5499646803:ℚ)/10490000000),((-5750489629:ℚ)/13171875000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((3637753727:ℚ)/10000000000),((2085111565467088161513014924031371913787:ℚ)/7279988291015625000000000000000000000000),((1755648359904619237784177:ℚ)/5776000000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7132622909:ℚ)/10000000000),((3628799101:ℚ)/5000000000),((-2764799101:ℚ)/5268750000),((-46273606181:ℚ)/105850000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((3525275719:ℚ)/10000000000),((2705084248622298734098631194499819451791:ℚ)/9445159567500000000000000000000000000000),((111889782760597437075714817:ℚ)/369664000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((7162585839:ℚ)/10000000000),((7317493863:ℚ)/10000000000),((-5589493863:ℚ)/10585000000),((-46543272551:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((3409258423:ℚ)/10000000000),((5790980126638814334595342639208443938517:ℚ)/20122508400000000000000000000000000000000),((334249774705783132812170891:ℚ)/1108992000000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/8),((-9:ℚ)/16),((7222504249:ℚ)/10000000000),((295095209:ℚ)/400000000),((-225975209:ℚ)/427200000),((-47082538241:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3165034647:ℚ)/10000000000),((1486639507275734676347594785753018091837:ℚ)/5166477812500000000000000000000000000000),((110465771691418836623098857:ℚ)/369664000000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((1820603237:ℚ)/2500000000),((1487451507:ℚ)/2000000000),((-1141851507:ℚ)/2155000000),((-11905429133:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2901106469:ℚ)/10000000000),((457877524488729979611902489197886867561:ℚ)/1591425746875000000000000000000000000000),((18959320310215396659753:ℚ)/64000000000000000000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((7342312193:ℚ)/10000000000),((1889246487:ℚ)/2500000000),((-1457246487:ℚ)/2717500000),((-609630503:ℚ)/1400000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((326437437:ℚ)/1250000000),((2320274233117430486230430346924910651:ℚ)/7989450000000000000000000000000000000),((108546377638832714943326393:ℚ)/369664000000000000000000000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((3731041659:ℚ)/5000000000),((1949086033:ℚ)/2500000000),((-1517086033:ℚ)/2765000000),((-24619374931:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1907987643:ℚ)/10000000000),((205759078448767868981787302114004934331:ℚ)/695895200000000000000000000000000000000),((79952477424091284503494451:ℚ)/277248000000000000000000000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((7701522569:ℚ)/10000000000),((273521143:ℚ)/312500000),((-219521143:ℚ)/357500000),((-51393703121:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((652006777120704406385147339987182748287:ℚ)/2001542400000000000000000000000000000000),((36127351:ℚ)/128000000)⟩
theorem valid12 : Valid source29 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((2164532699:ℚ)/2500000000),((2665426671:ℚ)/2500000000),((-248158519:ℚ)/360000000),((-15000794291:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((6428125081612908255235381570427774561:ℚ)/18000000000000000000000000000000000000),((36127351:ℚ)/128000000)⟩
theorem valid13 : Valid source29 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((5283776511:ℚ)/5000000000),((14472276503:ℚ)/10000000000),((-12744276503:ℚ)/16000000000),((-38593988599:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2515225480847479759563421579:ℚ)/6094080000000000000000000000),((36127351:ℚ)/128000000)⟩
theorem valid14 : Valid source29 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source29 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source29 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source29 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source29 nn0 nn1 Qcell ((2117:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source29 nn0 nn1 Qcell ((2117:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC07
#check @N11Formalization.C450Source29GroupedC07.bound
#print axioms N11Formalization.C450Source29GroupedC07.valid0
#print axioms N11Formalization.C450Source29GroupedC07.valid1
#print axioms N11Formalization.C450Source29GroupedC07.valid2
#print axioms N11Formalization.C450Source29GroupedC07.valid3
#print axioms N11Formalization.C450Source29GroupedC07.valid4
#print axioms N11Formalization.C450Source29GroupedC07.valid5
#print axioms N11Formalization.C450Source29GroupedC07.valid6
#print axioms N11Formalization.C450Source29GroupedC07.valid7
#print axioms N11Formalization.C450Source29GroupedC07.valid8
#print axioms N11Formalization.C450Source29GroupedC07.valid9
#print axioms N11Formalization.C450Source29GroupedC07.valid10
#print axioms N11Formalization.C450Source29GroupedC07.valid11
#print axioms N11Formalization.C450Source29GroupedC07.valid12
#print axioms N11Formalization.C450Source29GroupedC07.valid13
#print axioms N11Formalization.C450Source29GroupedC07.valid14
#print axioms N11Formalization.C450Source29GroupedC07.bound
#print axioms N11Formalization.C450Source29GroupedC07.endpoint_checks
