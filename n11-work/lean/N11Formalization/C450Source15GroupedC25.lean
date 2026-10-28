import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((36673047:ℚ)/62500000),((3199895833:ℚ)/5000000000),((43173047:ℚ)/83437500),((33279062497:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1377427423:ℚ)/2000000000),((-120829773120698732072432267:ℚ)/48406379699707031250000000000),((-877514140199524485902693:ℚ)/3610000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6343922583:ℚ)/10000000000),((6637815327:ℚ)/10000000000),((7383922583:ℚ)/13825000000),((68700337943:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5831601187:ℚ)/10000000000),((-112500089694511403219930200771100014234676488841606497:ℚ)/16514880566406250000000000000000000000000000000000000000),((-3550430865544790513251923:ℚ)/14440000000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((6581976237:ℚ)/10000000000),((1718951023:ℚ)/2500000000),((7621976237:ℚ)/14300000000),((17710559207:ℚ)/27650000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5235505717:ℚ)/10000000000),((-131846952743386764643819794384003220902461574387808667:ℚ)/18276293750000000000000000000000000000000000000000000000),((-1784671150919846341515109:ℚ)/7220000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((681999299:ℚ)/1000000000),((6994786461:ℚ)/10000000000),((785999299:ℚ)/1453750000),((6537552559:ℚ)/10400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1142572569:ℚ)/2500000000),((-43249681824364233646611867633070927867567068242429:ℚ)/4800530233764648437500000000000000000000000000000000),((-3589445081215210614287977:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6938988663:ℚ)/10000000000),((7113761339:ℚ)/10000000000),((7978988663:ℚ)/14775000000),((72983852051:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((33612577:ℚ)/80000000),((-15317060787540463738795327962609963486966403193762251:ℚ)/1679891528320312500000000000000000000000000000000000000),((-3598844198091741036830027:ℚ)/14440000000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((1411595283:ℚ)/2000000000),((7173246081:ℚ)/10000000000),((1619595283:ℚ)/2978750000),((73519214729:ℚ)/118200000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3799555903:ℚ)/10000000000),((-1642358480300330837529387171035309218807862359748357:ℚ)/165189402917480468750000000000000000000000000000000000),((-3608874905060250928636707:ℚ)/14440000000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((7117467439:ℚ)/10000000000),((3616364541:ℚ)/5000000000),((8157467439:ℚ)/15012500000),((37027280869:ℚ)/59575000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((447823183:ℚ)/1250000000),((-13185931527078481651924846454534119218928036897438289:ℚ)/1321658020782470703125000000000000000000000000000000000),((-1806780200476282557930169:ℚ)/7220000000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((3588478311:ℚ)/5000000000),((294067601:ℚ)/400000000),((4108478311:ℚ)/7625000000),((3005008409:ℚ)/4804000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((167612371:ℚ)/500000000),((-25748056732866228079695065344360887013721314348310121:ℚ)/2770764160156250000000000000000000000000000000000000000),((-5788121228081389299137:ℚ)/23104000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((3647964819:ℚ)/5000000000),((3735322241:ℚ)/5000000000),((4167964819:ℚ)/7743750000),((38097900169:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((709567931:ℚ)/2500000000),((-2263870384330397437690041128551420431374199389741183:ℚ)/241853703689575195312500000000000000000000000000000000),((-113340883934446971463009:ℚ)/451250000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((1853723949:ℚ)/2500000000),((7589592747:ℚ)/10000000000),((2113723949:ℚ)/3931250000),((77266334723:ℚ)/123900000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2211575511:ℚ)/10000000000),((-3491687272898305435040146929893278587823871268531:ℚ)/370827598869800567626953125000000000000000000000000),((-3636218667313854541040133:ℚ)/14440000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((470865963:ℚ)/625000000),((1565494359:ℚ)/2000000000),((535865963:ℚ)/1012500000),((15881449231:ℚ)/25160000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1320294633:ℚ)/10000000000),((-653099867150254953610926675216738647220359286413:ℚ)/80090332031250000000000000000000000000000000000000),((-3070968147015269:ℚ)/12160000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((3885878073:ℚ)/5000000000),((1216231857:ℚ)/1250000000),((4405878073:ℚ)/10000000000),((12066086713:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((647268097813124650492364761023131:ℚ)/125000000000000000000000000000000000),((-32378603:ℚ)/128000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((9674275497:ℚ)/10000000000),((13532650219:ℚ)/10000000000),((10714275497:ℚ)/27600000000),((130753851971:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((6556742506006006901780681:ℚ)/380880000000000000000000000),((-32378603:ℚ)/128000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((2383:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((2383:ℚ)/3200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((2383:ℚ)/3200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source15 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source15 nn0 nn1 Qcell ((2383:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC25
#check @N11Formalization.C450Source15GroupedC25.bound
#print axioms N11Formalization.C450Source15GroupedC25.valid0
#print axioms N11Formalization.C450Source15GroupedC25.valid1
#print axioms N11Formalization.C450Source15GroupedC25.valid2
#print axioms N11Formalization.C450Source15GroupedC25.valid3
#print axioms N11Formalization.C450Source15GroupedC25.valid4
#print axioms N11Formalization.C450Source15GroupedC25.valid5
#print axioms N11Formalization.C450Source15GroupedC25.valid6
#print axioms N11Formalization.C450Source15GroupedC25.valid7
#print axioms N11Formalization.C450Source15GroupedC25.valid8
#print axioms N11Formalization.C450Source15GroupedC25.valid9
#print axioms N11Formalization.C450Source15GroupedC25.valid10
#print axioms N11Formalization.C450Source15GroupedC25.valid11
#print axioms N11Formalization.C450Source15GroupedC25.valid12
#print axioms N11Formalization.C450Source15GroupedC25.bound
#print axioms N11Formalization.C450Source15GroupedC25.endpoint_checks
