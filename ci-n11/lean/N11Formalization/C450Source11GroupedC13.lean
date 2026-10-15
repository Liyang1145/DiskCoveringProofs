import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((625740761:ℚ)/1000000000),((1631459739:ℚ)/2500000000),((-1271459739:ℚ)/6200000000),((-1237222283:ℚ)/10300000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6035197497:ℚ)/10000000000),((21056679971615314314888499500750048728685272874707598311:ℚ)/635147568750000000000000000000000000000000000000000000000),((534825962413951101866671:ℚ)/21660000000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((1623820131:ℚ)/2500000000),((270550183:ℚ)/400000000),((-212950183:ℚ)/1030000000),((-3271460393:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((218374017:ℚ)/400000000),((100738554364456063736760292213922798794498701927712188671:ℚ)/3063310607812500000000000000000000000000000000000000000000),((4243808061028919886813:ℚ)/184832000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((6733126843:ℚ)/10000000000),((344135073:ℚ)/500000000),((-90711691:ℚ)/445000000),((-13799380529:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2411421769:ℚ)/5000000000),((23096713238127443920585775450181182391674015477747822724721:ℚ)/714428311043750000000000000000000000000000000000000000000000),((18344563521299860594279:ℚ)/866400000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((856505113:ℚ)/1250000000),((1750410391:ℚ)/2500000000),((-1390410391:ℚ)/6793750000),((-1769515339:ℚ)/13825000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((559222951:ℚ)/1250000000),((27124651016017893369871528556205054595393345179105924871:ℚ)/841484773860168457031250000000000000000000000000000000000),((146640268739892173476477:ℚ)/7220000000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((1742737329:ℚ)/2500000000),((3530554591:ℚ)/5000000000),((-2810554591:ℚ)/13825000000),((-3628211987:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((25607849:ℚ)/62500000),((149868228806695812557457479818345484102537840141186097531:ℚ)/4685046609667205810546875000000000000000000000000000000000),((560785410466336235351277:ℚ)/28880000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((1406080299:ℚ)/2000000000),((7120575233:ℚ)/10000000000),((-5680575233:ℚ)/27887500000),((-2938240897:ℚ)/22500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3896216757:ℚ)/10000000000),((59466497819489264646286516685947106598479961451432784309:ℚ)/1861265945434570312500000000000000000000000000000000000000),((2193370981740883005610413:ℚ)/115520000000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((443115773:ℚ)/625000000),((1436007951:ℚ)/2000000000),((-127556439:ℚ)/625000000),((-929347319:ℚ)/7090625000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((3684817:ℚ)/10000000),((177757389168585375926201539672496094800605652668631:ℚ)/5570235781192779541015625000000000000000000000000000),((257235718709309158150951:ℚ)/13862400000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((7149301967:ℚ)/10000000000),((3619751393:ℚ)/5000000000),((-2899751393:ℚ)/14181250000),((-15047905901:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3461154459:ℚ)/10000000000),((676796566439257607362852473173668065739520912141323063905169:ℚ)/21232082185600000000000000000000000000000000000000000000000000),((523480408926747151025133:ℚ)/28880000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((3604375163:ℚ)/5000000000),((1459792873:ℚ)/2000000000),((-1171792873:ℚ)/5720000000),((-7613125489:ℚ)/57675000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((644534489:ℚ)/2000000000),((58165475917884141910523752563378570916149666421337599:ℚ)/1826701008899688720703125000000000000000000000000000000),((81769715632177630637693:ℚ)/4620800000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((7268197473:ℚ)/10000000000),((3679212263:ℚ)/5000000000),((-2959212263:ℚ)/14418750000),((-15404592419:ℚ)/116300000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1482896691:ℚ)/5000000000),((721468022495187026722668674405311302335241389927655395255777:ℚ)/22681238014556250000000000000000000000000000000000000000000000),((498648682340184134417373:ℚ)/28880000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-1:ℚ)/4),((-3:ℚ)/16),((91595543:ℚ)/125000000),((927235413:ℚ)/1250000000),((-747235413:ℚ)/3634375000),((-194786629:ℚ)/1465625000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((134261871:ℚ)/500000000),((2181585163204215935683474620873596778817846542804028109:ℚ)/68651428737831115722656250000000000000000000000000000000),((91170802628615442421519:ℚ)/5415000000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((1477417651:ℚ)/2000000000),((7477340733:ℚ)/10000000000),((-6037340733:ℚ)/29312500000),((-3152252953:ℚ)/23640000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2372614311:ℚ)/10000000000),((102453815473072160304105252972445180315482485721475123751:ℚ)/3227111943300000000000000000000000000000000000000000000000),((5686170137744021645954239:ℚ)/346560000000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((3723265973:ℚ)/5000000000),((1543031517:ℚ)/2000000000),((-418343839:ℚ)/1970000000),((-7969797919:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2013032243:ℚ)/10000000000),((26953974517497018428881594358237203197782891829804794935529:ℚ)/838411068750000000000000000000000000000000000000000000000000),((12810498335993:ℚ)/800000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((3842147997:ℚ)/5000000000),((1638147089:ℚ)/2000000000),((-1350147089:ℚ)/6100000000),((-8326443991:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1125977125203943340915492248635810912284829947125039200337:ℚ)/34579094400000000000000000000000000000000000000000000000000),((118577:ℚ)/8000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((4079888783:ℚ)/5000000000),((2523124297:ℚ)/2500000000),((-2163124297:ℚ)/8100000000),((-9039666349:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((9089143644524616485386384679327035049770992691775649587509:ℚ)/259200000000000000000000000000000000000000000000000000000000),((118577:ℚ)/8000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((5030622927:ℚ)/5000000000),((13894564149:ℚ)/10000000000),((-12454564149:ℚ)/40000000000),((-11891868781:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((246570972523477071443991765799751223920323805366612623543:ℚ)/6307372800000000000000000000000000000000000000000000000000),((118577:ℚ)/8000000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC13
#check @N11Formalization.C450Source11GroupedC13.bound
#print axioms N11Formalization.C450Source11GroupedC13.valid0
#print axioms N11Formalization.C450Source11GroupedC13.valid1
#print axioms N11Formalization.C450Source11GroupedC13.valid2
#print axioms N11Formalization.C450Source11GroupedC13.valid3
#print axioms N11Formalization.C450Source11GroupedC13.valid4
#print axioms N11Formalization.C450Source11GroupedC13.valid5
#print axioms N11Formalization.C450Source11GroupedC13.valid6
#print axioms N11Formalization.C450Source11GroupedC13.valid7
#print axioms N11Formalization.C450Source11GroupedC13.valid8
#print axioms N11Formalization.C450Source11GroupedC13.valid9
#print axioms N11Formalization.C450Source11GroupedC13.valid10
#print axioms N11Formalization.C450Source11GroupedC13.valid11
#print axioms N11Formalization.C450Source11GroupedC13.valid12
#print axioms N11Formalization.C450Source11GroupedC13.valid13
#print axioms N11Formalization.C450Source11GroupedC13.valid14
#print axioms N11Formalization.C450Source11GroupedC13.valid15
#print axioms N11Formalization.C450Source11GroupedC13.bound
#print axioms N11Formalization.C450Source11GroupedC13.endpoint_checks
