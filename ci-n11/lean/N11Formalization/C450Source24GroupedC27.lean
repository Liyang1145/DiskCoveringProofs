import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((5531399433:ℚ)/10000000000),((6089557593:ℚ)/10000000000),((6939399433:ℚ)/10680000000),((81705133523:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7556649279:ℚ)/10000000000),((-20778682668968078826454242656807999:ℚ)/152273304000000000000000000000000000),((-16571710996542110430469417:ℚ)/44359680000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((3004490927:ℚ)/5000000000),((1582070373:ℚ)/2500000000),((3708490927:ℚ)/5530000000),((21082774103:ℚ)/26700000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1647293589:ℚ)/2500000000),((-35735073066145986588743764855534468417965317597674207:ℚ)/226489790625000000000000000000000000000000000000000000),((-1030258898624261662430257:ℚ)/2772480000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/8),((11:ℚ)/16),((3123819493:ℚ)/5000000000),((6447612207:ℚ)/10000000000),((425313277:ℚ)/625000000),((85643734277:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((94653249:ℚ)/156250000),((-127852255931194055704776887360162479444683089627577:ℚ)/762939453125000000000000000000000000000000000000000),((-16438268684239889826557017:ℚ)/44359680000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((6366938033:ℚ)/10000000000),((1313384699:ℚ)/2000000000),((7774938033:ℚ)/11440000000),((17391231689:ℚ)/22500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5776375307:ℚ)/10000000000),((-71182144051743823419976915696544894065690516384556783:ℚ)/425339200000000000000000000000000000000000000000000000),((-218354929725896094827611:ℚ)/591462400000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((40538867:ℚ)/62500000),((3343108159:ℚ)/5000000000),((49338867:ℚ)/72687500),((3394937673:ℚ)/4400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((685283929:ℚ)/1250000000),((-50140433609471819250240346901099918081444581083:ℚ)/300033139610290527343750000000000000000000000000),((-71550818172070291954689:ℚ)/194560000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((1321096391:ℚ)/2000000000),((6805491573:ℚ)/10000000000),((1602696391:ℚ)/2364000000),((89580407303:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2586653967:ℚ)/5000000000),((-5166809002735306021144357580651338334006912777800177:ℚ)/30963760650000000000000000000000000000000000000000000),((-45011549264357200078537:ℚ)/122880000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((3362364293:ℚ)/5000000000),((6924750103:ℚ)/10000000000),((4066364293:ℚ)/6005000000),((90892251133:ℚ)/118200000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((484661503:ℚ)/1000000000),((-338217631398779027417827056893788072497185568173656051:ℚ)/2030066719921875000000000000000000000000000000000000000),((-5394456033082911406869699:ℚ)/14786560000000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((427747463:ℚ)/625000000),((3521996347:ℚ)/5000000000),((515747463:ℚ)/762500000),((46101959817:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2249150677:ℚ)/5000000000),((-230430945419999631599960051245228608127211989585667:ℚ)/1385382080078125000000000000000000000000000000000000),((-1343015260612086011841499:ℚ)/3696640000000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((1392635033:ℚ)/2000000000),((3581610043:ℚ)/5000000000),((1674235033:ℚ)/2478000000),((46757710473:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((41228587:ℚ)/100000000),((-31331318061698487490243149433234922449368263159419:ℚ)/188691956250000000000000000000000000000000000000000),((-1337301208142921013213339:ℚ)/3696640000000000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((1770594139:ℚ)/2500000000),((3641216487:ℚ)/5000000000),((2122594139:ℚ)/3145000000),((47413381357:ℚ)/61950000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((3712029881:ℚ)/10000000000),((-15734780857333543515707366835781200843161670267431:ℚ)/94931865310668945312500000000000000000000000000000),((-210232399097198839664083:ℚ)/583680000000000000000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((1800391059:ℚ)/2500000000),((1504163561:ℚ)/2000000000),((2152391059:ℚ)/3240000000),((19489799171:ℚ)/25160000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((3252394477:ℚ)/10000000000),((-618883636417103214392076534924464806095745396118933:ℚ)/3936600000000000000000000000000000000000000000000000),((-210923157020045325492931:ℚ)/591462400000000000000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((1487980179:ℚ)/2000000000),((94263771:ℚ)/100000000),((1769580179:ℚ)/3200000000),((1184101481:ℚ)/1296000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1028106281:ℚ)/5000000000),((-1420030038138570726453731014302409866224068666836773:ℚ)/19200000000000000000000000000000000000000000000000000),((-69251531711742099:ℚ)/194560000000000000)⟩
theorem valid11 : Valid source24 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((9345157851:ℚ)/10000000000),((13232891571:ℚ)/10000000000),((10753157851:ℚ)/22080000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-2010420554138501897769007:ℚ)/121881600000000000000000000),((-22807963:ℚ)/64000000)⟩
theorem valid12 : Valid source24 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source24 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((1239:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source24 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source24 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC27
#check @N11Formalization.C450Source24GroupedC27.bound
#print axioms N11Formalization.C450Source24GroupedC27.valid0
#print axioms N11Formalization.C450Source24GroupedC27.valid1
#print axioms N11Formalization.C450Source24GroupedC27.valid2
#print axioms N11Formalization.C450Source24GroupedC27.valid3
#print axioms N11Formalization.C450Source24GroupedC27.valid4
#print axioms N11Formalization.C450Source24GroupedC27.valid5
#print axioms N11Formalization.C450Source24GroupedC27.valid6
#print axioms N11Formalization.C450Source24GroupedC27.valid7
#print axioms N11Formalization.C450Source24GroupedC27.valid8
#print axioms N11Formalization.C450Source24GroupedC27.valid9
#print axioms N11Formalization.C450Source24GroupedC27.valid10
#print axioms N11Formalization.C450Source24GroupedC27.valid11
#print axioms N11Formalization.C450Source24GroupedC27.valid12
#print axioms N11Formalization.C450Source24GroupedC27.bound
#print axioms N11Formalization.C450Source24GroupedC27.endpoint_checks
