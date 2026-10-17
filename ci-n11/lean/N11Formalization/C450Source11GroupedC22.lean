import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((3019450677:ℚ)/5000000000),((409608401:ℚ)/625000000),((1198483559:ℚ)/3560000000),((1428825203:ℚ)/3100000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1304921151:ℚ)/2000000000),((740020154847913241131913872091725159:ℚ)/58993627750000000000000000000000000000),((-143874587476277474362315963:ℚ)/1108992000000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((3257346207:ℚ)/5000000000),((169788399:ℚ)/250000000),((3833346207:ℚ)/11060000000),((589365197:ℚ)/1335000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5409956241:ℚ)/10000000000),((144130337337334871959307909690392713579270458714995324921:ℚ)/13642543014532031250000000000000000000000000000000000000000),((-147522740973063539157216403:ℚ)/1108992000000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/16),((3:ℚ)/8),((3376273541:ℚ)/5000000000),((6910429079:ℚ)/10000000000),((3952273541:ℚ)/11250000000),((23931287237:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4767456003:ℚ)/10000000000),((118710534830697696612050685375044319347111671630665855781:ℚ)/12230448693750000000000000000000000000000000000000000000000),((-49784863486943751370876169:ℚ)/369664000000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((1717866353:ℚ)/2500000000),((1757329359:ℚ)/2500000000),((2005866353:ℚ)/5720000000),((6071988077:ℚ)/14062500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1103583539:ℚ)/2500000000),((3401978757042523478272529120852911752263926807599596004683:ℚ)/355418229103088378906250000000000000000000000000000000000000),((-12522705578097354561161041:ℚ)/92416000000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((5:ℚ)/16),((3:ℚ)/8),((6990378139:ℚ)/10000000000),((3544379951:ℚ)/5000000000),((8142378139:ℚ)/23070000000),((1112103623:ℚ)/2600000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((161304001:ℚ)/400000000),((447720819639386525144719078421598503488214591259859620451:ℚ)/48720754387500000000000000000000000000000000000000000000000),((-201588863184096625896835529:ℚ)/1478656000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((881229061:ℚ)/1250000000),((446762579:ℚ)/625000000),((1025229061:ℚ)/2907500000),((1540287737:ℚ)/3604687500),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((957086213:ℚ)/2500000000),((48231544089306178864781972624811930889565820040746433249:ℚ)/5279357172877015113830566406250000000000000000000000000000),((-3159410983647049044037129:ℚ)/23104000000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((5:ℚ)/16),((3:ℚ)/8),((3554642769:ℚ)/5000000000),((7207641549:ℚ)/10000000000),((4130642769:ℚ)/11725000000),((24822924647:ℚ)/58150000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((722632639:ℚ)/2000000000),((1841896173507049104120970203191153879424896999217202735053211:ℚ)/202738450703828320312500000000000000000000000000000000000000000),((-152112133753499482819676467:ℚ)/1108992000000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((7168737321:ℚ)/10000000000),((7267080783:ℚ)/10000000000),((2773579107:ℚ)/7880000000),((25001242349:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1692483811:ℚ)/5000000000),((110415373622769200297961528169175626921649757889853966668739:ℚ)/12218026014956665039062500000000000000000000000000000000000000),((-610291468917612403904391427:ℚ)/4435968000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((5:ℚ)/16),((3:ℚ)/8),((1807046967:ℚ)/2500000000),((7326518991:ℚ)/10000000000),((2095046967:ℚ)/5957500000),((25179556973:ℚ)/59100000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3140918359:ℚ)/10000000000),((197632717273469633954072245531516838156140821939039195096886609:ℚ)/21979195875223481250000000000000000000000000000000000000000000000),((-38258481965435934899711683:ℚ)/277248000000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((7287637207:ℚ)/10000000000),((3692978099:ℚ)/5000000000),((8439637207:ℚ)/24020000000),((12678934297:ℚ)/29787500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1438489393:ℚ)/5000000000),((133269671004090360884544427486582424981486351651543197847223:ℚ)/14891834997348546600341796875000000000000000000000000000000000),((-566926374319139935150041:ℚ)/4096000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((7347085369:ℚ)/10000000000),((75048277:ℚ)/100000000),((8499085369:ℚ)/24400000000),((257144831:ℚ)/600500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2587062821:ℚ)/10000000000),((46102289030074378130309804353460212807687927339870521:ℚ)/5035918843219531250000000000000000000000000000000000000),((-205276041873629853785126689:ℚ)/1478656000000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((7465978267:ℚ)/10000000000),((3871279839:ℚ)/5000000000),((8617978267:ℚ)/25160000000),((13213839517:ℚ)/30500000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1880771789:ℚ)/10000000000),((167422654319109323774883532809023068062792990930407585151323:ℚ)/17539646449414062500000000000000000000000000000000000000000000),((-206508594637736307497916361:ℚ)/1478656000000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((1925937773:ℚ)/2500000000),((7980278033:ℚ)/10000000000),((2213937773:ℚ)/6480000000),((27140834099:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((95960820803839321796112197579120654080874891177177368543781:ℚ)/10204741112681250000000000000000000000000000000000000000000000),((-71987583:ℚ)/512000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((1985376973:ℚ)/2500000000),((1976330221:ℚ)/2000000000),((2273376973:ℚ)/8000000000),((6568990663:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((839510758159648777468663402526723:ℚ)/60000000000000000000000000000000000),((-71987583:ℚ)/512000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((9843122633:ℚ)/10000000000),((13683262259:ℚ)/10000000000),((10995122633:ℚ)/44160000000),((44249786777:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((4776952216116804138131011:ℚ)/243763200000000000000000000),((-71987583:ℚ)/512000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC22
#check @N11Formalization.C450Source11GroupedC22.bound
#print axioms N11Formalization.C450Source11GroupedC22.valid0
#print axioms N11Formalization.C450Source11GroupedC22.valid1
#print axioms N11Formalization.C450Source11GroupedC22.valid2
#print axioms N11Formalization.C450Source11GroupedC22.valid3
#print axioms N11Formalization.C450Source11GroupedC22.valid4
#print axioms N11Formalization.C450Source11GroupedC22.valid5
#print axioms N11Formalization.C450Source11GroupedC22.valid6
#print axioms N11Formalization.C450Source11GroupedC22.valid7
#print axioms N11Formalization.C450Source11GroupedC22.valid8
#print axioms N11Formalization.C450Source11GroupedC22.valid9
#print axioms N11Formalization.C450Source11GroupedC22.valid10
#print axioms N11Formalization.C450Source11GroupedC22.valid11
#print axioms N11Formalization.C450Source11GroupedC22.valid12
#print axioms N11Formalization.C450Source11GroupedC22.valid13
#print axioms N11Formalization.C450Source11GroupedC22.valid14
#print axioms N11Formalization.C450Source11GroupedC22.bound
#print axioms N11Formalization.C450Source11GroupedC22.endpoint_checks
