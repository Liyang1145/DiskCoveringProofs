import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((5951422597:ℚ)/10000000000),((1298124759:ℚ)/2000000000),((30014267791:ℚ)/106800000000),((1938124759:ℚ)/4960000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6711903493:ℚ)/10000000000),((165413372066420727573876213029153569043:ℚ)/2174741093376000000000000000000000000000),((-8186307556571542041727451:ℚ)/27724800000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((6429903843:ℚ)/10000000000),((6729571197:ℚ)/10000000000),((31449711529:ℚ)/110600000000),((9929571197:ℚ)/26700000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2811417127:ℚ)/5000000000),((362541136913774774183992764077104512720450786520607825981789:ℚ)/5197159243631250000000000000000000000000000000000000000000000),((-214617647544799666573108739:ℚ)/693120000000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((833620407:ℚ)/1250000000),((348421081:ℚ)/500000000),((309297017:ℚ)/1100000000),((72631583:ℚ)/197500000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5001822643:ℚ)/10000000000),((399674728569756489718296185811143255393722102609057:ℚ)/5825949121093750000000000000000000000000000000000000),((-182624807891949537419177:ℚ)/577600000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((6907918117:ℚ)/10000000000),((1771953367:ℚ)/2500000000),((32883754351:ℚ)/116300000000),((2571953367:ℚ)/7150000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((860139867:ℚ)/2000000000),((51205108264275199672936828645459495962144996439820858924353:ℚ)/772498386285742187500000000000000000000000000000000000000000),((-4668696140009604734560073:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((3513679791:ℚ)/5000000000),((180179613:ℚ)/250000000),((16621039373:ℚ)/59100000000),((260179613:ℚ)/726875000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3906740691:ℚ)/10000000000),((9211636414104634326834311316720615392916936561641069153:ℚ)/139727833381629180908203125000000000000000000000000000000),((-141464370535932474504899:ℚ)/433200000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((1786694657:ℚ)/2500000000),((7326535771:ℚ)/10000000000),((8400083971:ℚ)/30025000000),((3508845257:ℚ)/9850000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1735464079:ℚ)/5000000000),((565263909445980001307717874202405844177152042406157968096287:ℚ)/8615385672322656250000000000000000000000000000000000000000000),((-76193556120236541556400337:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((1816544083:ℚ)/2500000000),((7445868157:ℚ)/10000000000),((8489632249:ℚ)/30500000000),((10645868157:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1487439793:ℚ)/5000000000),((41130205250431306671099296032851090536088109512001372421787:ℚ)/629489855402441406250000000000000000000000000000000000000000),((-76936821858812379543969793:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((3692776851:ℚ)/5000000000),((960559973:ℚ)/1250000000),((17158330553:ℚ)/62900000000),((1360559973:ℚ)/3812500000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1190594853:ℚ)/5000000000),((2273616960549931513689213888508528122200915059277407145323:ℚ)/34257121971511840820312500000000000000000000000000000000000),((-638415424882663:ℚ)/1900000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((190606279:ℚ)/250000000),((7923025791:ℚ)/10000000000),((875818837:ℚ)/3240000000),((11123025791:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((84146167004643423759376646991215280420047669232725890469161:ℚ)/1275592639085156250000000000000000000000000000000000000000000),((-42873:ℚ)/125000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((982859737:ℚ)/1250000000),((307174887:ℚ)/312500000),((4468579211:ℚ)/20000000000),((407174887:ℚ)/1012500000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((127687149655658329966482891808629507633463815532717:ℚ)/1621829223632812500000000000000000000000000000000000),((-42873:ℚ)/125000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((4884977431:ℚ)/5000000000),((6818646703:ℚ)/5000000000),((20734932293:ℚ)/110400000000),((8418646703:ℚ)/20000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((953414672086647545851143064918991232091:ℚ)/9522000000000000000000000000000000000000),((-42873:ℚ)/125000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC20
#check @N11Formalization.C450Source21GroupedC20.bound
#print axioms N11Formalization.C450Source21GroupedC20.valid0
#print axioms N11Formalization.C450Source21GroupedC20.valid1
#print axioms N11Formalization.C450Source21GroupedC20.valid2
#print axioms N11Formalization.C450Source21GroupedC20.valid3
#print axioms N11Formalization.C450Source21GroupedC20.valid4
#print axioms N11Formalization.C450Source21GroupedC20.valid5
#print axioms N11Formalization.C450Source21GroupedC20.valid6
#print axioms N11Formalization.C450Source21GroupedC20.valid7
#print axioms N11Formalization.C450Source21GroupedC20.valid8
#print axioms N11Formalization.C450Source21GroupedC20.valid9
#print axioms N11Formalization.C450Source21GroupedC20.valid10
#print axioms N11Formalization.C450Source21GroupedC20.bound
#print axioms N11Formalization.C450Source21GroupedC20.endpoint_checks
