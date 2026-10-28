import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((237469373:ℚ)/400000000),((646398869:ℚ)/1000000000),((1739085611:ℚ)/2136000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((842864859:ℚ)/1250000000),((-62219118819506928324921240019072177:ℚ)/3045466080000000000000000000000000000),((-4744211729600518000324403:ℚ)/29573120000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((6411788817:ℚ)/10000000000),((3350761721:ℚ)/5000000000),((46802521719:ℚ)/55300000000),((10500285163:ℚ)/10680000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5667386509:ℚ)/10000000000),((-24321726527051021110441572509338209489305427799989886977:ℚ)/1056952356250000000000000000000000000000000000000000000000),((-118011381684322391184542043:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/8),((15:ℚ)/16),((1329862651:ℚ)/2000000000),((6820289937:ℚ)/10000000000),((9693038557:ℚ)/11250000000),((21356869811:ℚ)/22120000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5055471283:ℚ)/10000000000),((-71903861314056244217795315858555338636079905805678617:ℚ)/2966308593750000000000000000000000000000000000000000000),((-470854823183085808430588587:ℚ)/2957312000000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((3384037427:ℚ)/5000000000),((1734763971:ℚ)/2500000000),((1896020153:ℚ)/2200000000),((5428291913:ℚ)/5625000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((295171189:ℚ)/625000000),((-146622028470800157709412519987485010052057577949829:ℚ)/6050000000000000000000000000000000000000000000000000),((-29353887436029503925003043:ℚ)/184832000000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((1721709017:ℚ)/2500000000),((6998438661:ℚ)/10000000000),((12531963119:ℚ)/14418750000),((21891315983:ℚ)/22880000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((545844541:ℚ)/1250000000),((-54501227075538119316688382248430811031313540587291:ℚ)/2195554097235202789306640625000000000000000000000000),((-469065166546321242687372883:ℚ)/2957312000000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((6946216537:ℚ)/10000000000),((705782131:ℚ)/1000000000),((50543515759:ℚ)/58150000000),((2206946393:ℚ)/2307000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((4178195753:ℚ)/10000000000),((-30496533483996873201530528733534509967407956275480617377:ℚ)/1228935739843750000000000000000000000000000000000000000000),((-4684676538723251641430403:ℚ)/29573120000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((7:ℚ)/8),((15:ℚ)/16),((1751399229:ℚ)/2500000000),((1779300959:ℚ)/2500000000),((12739794603:ℚ)/14656250000),((5561902877:ℚ)/5815000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3981262023:ℚ)/10000000000),((-488131013689366061987941320039046506040428414575535501:ℚ)/19676534461975097656250000000000000000000000000000000000),((-29241853806701654187140363:ℚ)/184832000000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((883122151:ℚ)/1250000000),((1401677:ℚ)/1953125),((6421855057:ℚ)/7387500000),((35040248:ℚ)/36640625),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((754928209:ℚ)/2000000000),((-5207780935455111690294177355988161115650383436742717:ℚ)/209986441040039062500000000000000000000000000000000000),((-71299924872426604593:ℚ)/451250000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((1424871483:ℚ)/2000000000),((3603138699:ℚ)/5000000000),((10358100381:ℚ)/11867500000),((11257416097:ℚ)/11820000000),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((222290059:ℚ)/625000000),((-262028846290517254687975897384695045380264840031865507:ℚ)/10446185617480468750000000000000000000000000000000000000),((-116742942720935805761841523:ℚ)/739328000000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((7154047487:ℚ)/10000000000),((7235968527:ℚ)/10000000000),((51998332409:ℚ)/59575000000),((22603905581:ℚ)/23735000000),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((1721350707:ℚ)/5000000000),((-99426474309772836595760546080827494847422003027162929981:ℚ)/3964545670019531250000000000000000000000000000000000000000),((-466672234034966328468153067:ℚ)/2957312000000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((957:ℚ)/1280),((7:ℚ)/8),((15:ℚ)/16),((3591868769:ℚ)/5000000000),((7265659627:ℚ)/10000000000),((26103081383:ℚ)/29906250000),((22692978881:ℚ)/23830000000),((75681297:ℚ)/80000000),((2367032267:ℚ)/2500000000),((1650403157:ℚ)/5000000000),((3325020131:ℚ)/10000000000),((-804813008366384525840412618652024805459908830859123:ℚ)/32097198229980468750000000000000000000000000000000000),((-466372577097957048614409267:ℚ)/2957312000000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((2383:ℚ)/3200) ((957:ℚ)/1280) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((957:ℚ)/1280),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((721342757:ℚ)/1000000000),((3647675349:ℚ)/5000000000),((5241399299:ℚ)/6005000000),((11391026047:ℚ)/11962500000),((4726187811:ℚ)/5000000000),((946016213:ℚ)/1000000000),((831186567:ℚ)/2500000000),((1601592087:ℚ)/5000000000),((-25446579076046281821512286913071076190463523642740799:ℚ)/1015033359960937500000000000000000000000000000000000000),((-116518200018267029908243123:ℚ)/739328000000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((957:ℚ)/1280) ((1201:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((7243117581:ℚ)/10000000000),((7354732757:ℚ)/10000000000),((17540607689:ℚ)/20175000000),((22960198271:ℚ)/24020000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((3076699469:ℚ)/10000000000),((-953906778435309590731606110674739275566735088963207869:ℚ)/38493013403320312500000000000000000000000000000000000000),((-465472885720635561085237427:ℚ)/2957312000000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((1460499509:ℚ)/2000000000),((1482822941:ℚ)/2000000000),((10607496563:ℚ)/12200000000),((4627668823:ℚ)/4842000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((21931609:ℚ)/78125000),((-843540040084794863110372357693231782104552355323978407:ℚ)/34047150000000000000000000000000000000000000000000000000),((-18594899638811137845905763:ℚ)/118292480000000000000000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((7361877431:ℚ)/10000000000),((7532878283:ℚ)/10000000000),((53453142017:ℚ)/61950000000),((23494634849:ℚ)/24400000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2509857081:ℚ)/10000000000),((-999920816567887592782381817845708915677257764336633951:ℚ)/41276365429687500000000000000000000000000000000000000000),((-463670260134626512801167347:ℚ)/2957312000000000000000000000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((7480636979:ℚ)/10000000000),((153032829:ℚ)/200000000),((54284458853:ℚ)/62900000000),((477018487:ℚ)/495600000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((8873259:ℚ)/50000000),((-36797023332281994063907916663973598399110132463798219:ℚ)/1518909844970703125000000000000000000000000000000000000),((-160315077:ℚ)/1024000000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((3799698119:ℚ)/5000000000),((3944583313:ℚ)/5000000000),((27557886833:ℚ)/32400000000),((12281749939:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((63025163:ℚ)/5000000000),((-182785746124146594558214791772752610583430672125476397:ℚ)/7873200000000000000000000000000000000000000000000000000),((-160315077:ℚ)/1024000000)⟩
theorem valid16 : Valid eighth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound eighth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((3918456971:ℚ)/5000000000),((489466249:ℚ)/500000000),((28389198797:ℚ)/40000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-995132531770362595122295106680937464825292608974782833:ℚ)/75000000000000000000000000000000000000000000000000000000),((-160315077:ℚ)/1024000000)⟩
theorem valid17 : Valid eighth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((9737025299:ℚ)/10000000000),((13589510863:ℚ)/10000000000),((70079177093:ℚ)/110400000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-2708888199574385792718030427257712817:ℚ)/336393216000000000000000000000000000000),((-160315077:ℚ)/1024000000)⟩
theorem valid18 : Valid eighth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((4747:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((4747:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((4747:ℚ)/6400) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((4747:ℚ)/6400) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound eighth nn0 nn1 Qcell ((4747:ℚ)/6400) ((957:ℚ)/1280) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound eighth nn0 nn1 Qcell ((957:ℚ)/1280) ((61:ℚ)/80) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound eighth nn0 nn1 Qcell ((4747:ℚ)/6400) ((61:ℚ)/80) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound eighth nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound eighth nn0 nn1 Qcell ((4747:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC31
#check @N11Formalization.C450EighthGroupedC31.bound
#print axioms N11Formalization.C450EighthGroupedC31.valid0
#print axioms N11Formalization.C450EighthGroupedC31.valid1
#print axioms N11Formalization.C450EighthGroupedC31.valid2
#print axioms N11Formalization.C450EighthGroupedC31.valid3
#print axioms N11Formalization.C450EighthGroupedC31.valid4
#print axioms N11Formalization.C450EighthGroupedC31.valid5
#print axioms N11Formalization.C450EighthGroupedC31.valid6
#print axioms N11Formalization.C450EighthGroupedC31.valid7
#print axioms N11Formalization.C450EighthGroupedC31.valid8
#print axioms N11Formalization.C450EighthGroupedC31.valid9
#print axioms N11Formalization.C450EighthGroupedC31.valid10
#print axioms N11Formalization.C450EighthGroupedC31.valid11
#print axioms N11Formalization.C450EighthGroupedC31.valid12
#print axioms N11Formalization.C450EighthGroupedC31.valid13
#print axioms N11Formalization.C450EighthGroupedC31.valid14
#print axioms N11Formalization.C450EighthGroupedC31.valid15
#print axioms N11Formalization.C450EighthGroupedC31.valid16
#print axioms N11Formalization.C450EighthGroupedC31.valid17
#print axioms N11Formalization.C450EighthGroupedC31.valid18
#print axioms N11Formalization.C450EighthGroupedC31.bound
#print axioms N11Formalization.C450EighthGroupedC31.endpoint_checks
