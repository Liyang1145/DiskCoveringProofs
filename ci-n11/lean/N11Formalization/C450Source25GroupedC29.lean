import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((5394690273:ℚ)/10000000000),((2978602151:ℚ)/5000000000),((19864070819:ℚ)/26700000000),((46401827963:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7815428079:ℚ)/10000000000),((-1105595030039280737253336774069348269:ℚ)/4406056250000000000000000000000000000),((-4136283748170705930981207:ℚ)/11552000000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((5871497949:ℚ)/10000000000),((6195663097:ℚ)/10000000000),((21294493847:ℚ)/27650000000),((95903620261:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((687924447:ℚ)/1000000000),((-37011190823912842590751348590742682129949494444511404357:ℚ)/132119044531250000000000000000000000000000000000000000000),((-16257078792658718282632263:ℚ)/46208000000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/4),((13:ℚ)/16),((6109808141:ℚ)/10000000000),((197339627:ℚ)/312500000),((22009424423:ℚ)/28125000000),((3045415151:ℚ)/3456250000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((796169313:ℚ)/1250000000),((-4540466418590790479469849558142533019080528869009229973:ℚ)/15449523925781250000000000000000000000000000000000000000),((-7866957313535889685089:ℚ)/22562500000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((6228942611:ℚ)/10000000000),((6374464801:ℚ)/10000000000),((22366827833:ℚ)/28362500000),((98228042413:ℚ)/112500000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6100878089:ℚ)/10000000000),((-42862220005645680663917282170641050536753340470887463667:ℚ)/142598035998535156250000000000000000000000000000000000000),((-16038372683635294014810807:ℚ)/46208000000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((3144252497:ℚ)/5000000000),((1286811567:ℚ)/2000000000),((11272757491:ℚ)/14300000000),((19800550371:ℚ)/22690000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((5962719901:ℚ)/10000000000),((-1535172950115357434173365383770743827880313896446087:ℚ)/5112250000000000000000000000000000000000000000000000),((-638598513580916088668823:ℚ)/1848320000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((6348064251:ℚ)/10000000000),((3246823629:ℚ)/5000000000),((22724192753:ℚ)/28837500000),((49888707177:ℚ)/57200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((5821697411:ℚ)/10000000000),((-11241617690825759432010773229199496727919623236002949363:ℚ)/37470789926147460937500000000000000000000000000000000000),((-3972824745010257961425087:ℚ)/11552000000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((3203810229:ℚ)/5000000000),((6553233159:ℚ)/10000000000),((11451430687:ℚ)/14537500000),((33517343689:ℚ)/38450000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((5677594103:ℚ)/10000000000),((-230219596077092288546630550367691529499366470731970317:ℚ)/768084837402343750000000000000000000000000000000000000),((-15817381041575461885506567:ℚ)/46208000000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/4),((13:ℚ)/16),((1616793423:ℚ)/2500000000),((2116101:ℚ)/3200000),((5770380269:ℚ)/7328125000),((32424513:ℚ)/37216000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((553016601:ℚ)/1000000000),((-26304920502755816158082341493104349433917569132360457:ℚ)/87841671705245971679687500000000000000000000000000000),((-1612104597653432607:ℚ)/4731699200000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((261068961:ℚ)/400000000),((6672394739:ℚ)/10000000000),((930406883:ℚ)/1182000000),((102101131607:ℚ)/117250000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((537913659:ℚ)/1000000000),((-257333819809694187793471775652947193598520943274819:ℚ)/860104462500000000000000000000000000000000000000000),((-15668782680519325338042447:ℚ)/46208000000000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((6586271527:ℚ)/10000000000),((6731970581:ℚ)/10000000000),((23438814581:ℚ)/29787500000),((102875617553:ℚ)/118200000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((2612095143:ℚ)/5000000000),((-49379065417324754229732104077366605744646707481837308239:ℚ)/165189402917480468750000000000000000000000000000000000000),((-15594102141907195605622527:ℚ)/46208000000000000000000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((6645816267:ℚ)/10000000000),((679154323:ℚ)/1000000000),((23617448801:ℚ)/30025000000),((10365006199:ℚ)/11915000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((633120543:ℚ)/1250000000),((-3157841566167744534285261145110033881058890177756706459:ℚ)/10573264166259765625000000000000000000000000000000000000),((-155191672886446329692703:ℚ)/462080000000000000000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((670535831:ℚ)/1000000000),((431917453:ℚ)/625000000),((2379607493:ℚ)/3050000000),((6574926889:ℚ)/7506250000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((980207663:ℚ)/2000000000),((-51761676260548054211143957099792968295678623353536143:ℚ)/177328906250000000000000000000000000000000000000000000),((-60033337597504311049113:ℚ)/180500000000000000000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((6824434559:ℚ)/10000000000),((1757450843:ℚ)/2500000000),((24153303677:ℚ)/30975000000),((26686860959:ℚ)/30500000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2278514417:ℚ)/5000000000),((-4512419188922056442042136616282638826803024769123248469:ℚ)/15478637036132812500000000000000000000000000000000000000),((-951055229646257101625943:ℚ)/2888000000000000000000000)⟩
theorem valid12 : Valid source25 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((3471750381:ℚ)/5000000000),((7148916143:ℚ)/10000000000),((12255251143:ℚ)/15725000000),((108295909859:ℚ)/123900000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2093496753:ℚ)/5000000000),((-6910152776796464998069914359750743222461503711660037:ℚ)/23732966327667236328125000000000000000000000000000000),((-15064214650410107578731543:ℚ)/46208000000000000000000000)⟩
theorem valid13 : Valid source25 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source25 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((7062557377:ℚ)/10000000000),((3693554817:ℚ)/5000000000),((24867672131:ℚ)/32400000000),((55696212621:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((75665411:ℚ)/200000000),((-732160944957596652307673369975359527600387525546428921:ℚ)/2624400000000000000000000000000000000000000000000000000),((-3688955086629544936574823:ℚ)/11552000000000000000000000)⟩
theorem valid14 : Valid source25 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source25 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((456290221:ℚ)/625000000),((929146783:ℚ)/1000000000),((1598870663:ℚ)/2500000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((563207541:ℚ)/2000000000),((-978985922367786141762549863037027228162454884119837:ℚ)/6103515625000000000000000000000000000000000000000000),((-40101639:ℚ)/128000000)⟩
theorem valid15 : Valid source25 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((2301081929:ℚ)/2500000000),((13096576807:ℚ)/10000000000),((7823245787:ℚ)/13800000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-19612042405078270739219039116504793:ℚ)/219006000000000000000000000000000000),((-40101639:ℚ)/128000000)⟩
theorem valid16 : Valid source25 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source25 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source25 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source25 nn0 nn1 Qcell ((2269:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source25 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source25 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source25 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source25 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source25 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC29
#check @N11Formalization.C450Source25GroupedC29.bound
#print axioms N11Formalization.C450Source25GroupedC29.valid0
#print axioms N11Formalization.C450Source25GroupedC29.valid1
#print axioms N11Formalization.C450Source25GroupedC29.valid2
#print axioms N11Formalization.C450Source25GroupedC29.valid3
#print axioms N11Formalization.C450Source25GroupedC29.valid4
#print axioms N11Formalization.C450Source25GroupedC29.valid5
#print axioms N11Formalization.C450Source25GroupedC29.valid6
#print axioms N11Formalization.C450Source25GroupedC29.valid7
#print axioms N11Formalization.C450Source25GroupedC29.valid8
#print axioms N11Formalization.C450Source25GroupedC29.valid9
#print axioms N11Formalization.C450Source25GroupedC29.valid10
#print axioms N11Formalization.C450Source25GroupedC29.valid11
#print axioms N11Formalization.C450Source25GroupedC29.valid12
#print axioms N11Formalization.C450Source25GroupedC29.valid13
#print axioms N11Formalization.C450Source25GroupedC29.valid14
#print axioms N11Formalization.C450Source25GroupedC29.valid15
#print axioms N11Formalization.C450Source25GroupedC29.valid16
#print axioms N11Formalization.C450Source25GroupedC29.bound
#print axioms N11Formalization.C450Source25GroupedC29.endpoint_checks
