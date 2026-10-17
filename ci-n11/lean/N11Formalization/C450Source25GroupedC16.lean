import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC16
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((-1:ℚ)/16),(0:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/16),(0:ℚ),((1531306631:ℚ)/2500000000),((6429180511:ℚ)/10000000000),((8290819489:ℚ)/103000000000),((24:ℚ)/155),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((791895479:ℚ)/1250000000),((1588207903685717747211212654339:ℚ)/9876647468750000000000000000000),((-66870200301599249:ℚ)/243200000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/16),(0:ℚ),((1591379241:ℚ)/2500000000),((3334522651:ℚ)/5000000000),((1341825783:ℚ)/17800000000),((384:ℚ)/2575),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((577979871:ℚ)/1000000000),((214970349470861399030637570487698609439:ℚ)/1352420401093750000000000000000000000000),((-69869834711509439:ℚ)/243200000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((1651401393:ℚ)/2500000000),((678891481:ℚ)/1000000000),((793108519:ℚ)/10870000000),((64:ℚ)/445),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((32331119:ℚ)/62500000),((4074297285098438316073978256773404688187:ℚ)/26030297386281250000000000000000000000000),((-72866949577936247:ℚ)/243200000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((420348809:ℚ)/625000000),((6908745327:ℚ)/10000000000),((7811254673:ℚ)/110600000000),((768:ℚ)/5435),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((968841461:ℚ)/2000000000),((27342166212424506182739819027973701043283529:ℚ)/175343986654878125000000000000000000000000000),((-18591161626876511:ℚ)/60800000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/16),(0:ℚ),((6845513583:ℚ)/10000000000),((439283679:ℚ)/625000000),((480716321:ℚ)/7031250000),((384:ℚ)/2765),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((112339899:ℚ)/250000000),((58009280047267860201054004036023104763371:ℚ)/373243673515319824218750000000000000000000),((-303447239940945257:ℚ)/972800000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/16),(0:ℚ),((6965405697:ℚ)/10000000000),((1429659459:ℚ)/2000000000),((1514340541:ℚ)/22880000000),((256:ℚ)/1875),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4115528183:ℚ)/10000000000),((89128432197675661108621938903606744236321:ℚ)/575128125000000000000000000000000000000000),((-309433870297629863:ℚ)/972800000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((7085259343:ℚ)/10000000000),((726802237:ℚ)/1000000000),((745197763:ℚ)/11630000000),((96:ℚ)/715),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((925389697:ℚ)/2500000000),((9553430322380189564583287319082130930451:ℚ)/61799870902859375000000000000000000000000),((-315418579813244297:ℚ)/972800000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((7205076441:ℚ)/10000000000),((3693857861:ℚ)/5000000000),((3666142139:ℚ)/59100000000),((768:ℚ)/5815),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3237900707:ℚ)/10000000000),((14714564173145414737672348053659034038152663:ℚ)/95387534255192187500000000000000000000000000),((-321401464360068239:ℚ)/972800000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/16),(0:ℚ),((1464971757:ℚ)/2000000000),((7627013279:ℚ)/10000000000),((7092986721:ℚ)/122000000000),((128:ℚ)/985),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2699013359:ℚ)/10000000000),((5502844253665923478252538073980592015758779:ℚ)/35560541166250000000000000000000000000000000),((-65476522703752603:ℚ)/194560000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/16),(0:ℚ),((756432581:ℚ)/1000000000),((8105288907:ℚ)/10000000000),((6614711093:ℚ)/129600000000),((192:ℚ)/1525),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((969293477:ℚ)/10000000000),((18543960831284990917095877126162259025659:ℚ)/119137787280000000000000000000000000000000),((-33934003518279299:ℚ)/97280000000000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/16),(0:ℚ),((8042909919:ℚ)/10000000000),((1251907011:ℚ)/1250000000),((588092989:ℚ)/20000000000),((16:ℚ)/135),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((99023557574789340080012135202437849597:ℚ)/615093750000000000000000000000000000000),((-44884391:ℚ)/128000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/16),(0:ℚ),((9953813337:ℚ)/10000000000),((3456729811:ℚ)/2500000000),((223270189:ℚ)/55200000000),((12:ℚ)/125),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((17257756722716485388619829:ℚ)/95220000000000000000000000),((-44884391:ℚ)/128000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC16
#check @N11Formalization.C450Source25GroupedC16.bound
#print axioms N11Formalization.C450Source25GroupedC16.valid0
#print axioms N11Formalization.C450Source25GroupedC16.valid1
#print axioms N11Formalization.C450Source25GroupedC16.valid2
#print axioms N11Formalization.C450Source25GroupedC16.valid3
#print axioms N11Formalization.C450Source25GroupedC16.valid4
#print axioms N11Formalization.C450Source25GroupedC16.valid5
#print axioms N11Formalization.C450Source25GroupedC16.valid6
#print axioms N11Formalization.C450Source25GroupedC16.valid7
#print axioms N11Formalization.C450Source25GroupedC16.valid8
#print axioms N11Formalization.C450Source25GroupedC16.valid9
#print axioms N11Formalization.C450Source25GroupedC16.valid10
#print axioms N11Formalization.C450Source25GroupedC16.valid11
#print axioms N11Formalization.C450Source25GroupedC16.bound
#print axioms N11Formalization.C450Source25GroupedC16.endpoint_checks
