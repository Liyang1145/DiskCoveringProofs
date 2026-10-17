import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((590567437:ℚ)/1000000000),((645379521:ℚ)/1000000000),((3179702311:ℚ)/10680000000),((1013379521:ℚ)/2480000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6808111509:ℚ)/10000000000),((12196923500595460188328293214416781217:ℚ)/135921318336000000000000000000000000000),((-96743077871103752681221:ℚ)/277248000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((798161847:ℚ)/1250000000),((6693241851:ℚ)/10000000000),((4154485541:ℚ)/13825000000),((10373241851:ℚ)/26700000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((573199041:ℚ)/1000000000),((55597870895721828575901279245017976419256672852146077835237:ℚ)/690761671621875000000000000000000000000000000000000000000000),((-10178950705645326150678781:ℚ)/27724800000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((6624863691:ℚ)/10000000000),((1703228819:ℚ)/2500000000),((33954591073:ℚ)/112500000000),((2623228819:ℚ)/6912500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5121506519:ℚ)/10000000000),((130781655966242413144326672357123396920628851064124201:ℚ)/1706256793212890625000000000000000000000000000000000000),((-217291460014908849844047:ℚ)/577600000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((168614877:ℚ)/250000000),((6932557681:ℚ)/10000000000),((857844631:ℚ)/2860000000),((3537519227:ℚ)/9375000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((479020693:ℚ)/1000000000),((4017720823396629399792444749668663676935987961105037001217:ℚ)/52654552459716796875000000000000000000000000000000000000000),((-3511952883822134780845047:ℚ)/9241600000000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((6864293479:ℚ)/10000000000),((7052170609:ℚ)/10000000000),((34672880437:ℚ)/116300000000),((10732170609:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4436370713:ℚ)/10000000000),((1879212654430156097182638160497120798345608252592478181342059:ℚ)/24719948361143750000000000000000000000000000000000000000000000),((-3547008907753439745399287:ℚ)/9241600000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((698396053:ℚ)/1000000000),((7171755501:ℚ)/10000000000),((3503188159:ℚ)/11820000000),((10851755501:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((810812887:ℚ)/2000000000),((169451070425957332447490542135602799968110821367355899199317:ℚ)/2235645334106066894531250000000000000000000000000000000000000),((-10745496287539075721117581:ℚ)/27724800000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((7103597767:ℚ)/10000000000),((7291313707:ℚ)/10000000000),((35390793301:ℚ)/120100000000),((3657104569:ℚ)/9850000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((3634274779:ℚ)/10000000000),((977315114088143355833856397501135851198610652834898166636313:ℚ)/12923078508483984375000000000000000000000000000000000000000000),((-190338056213811799318917:ℚ)/486400000000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((7223206627:ℚ)/10000000000),((741084649:ℚ)/1000000000),((35749619881:ℚ)/122000000000),((1109084649:ℚ)/3002500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((197629:ℚ)/625000),((23765929589818055199007414518223920550830610789705081031:ℚ)/314744927701220703125000000000000000000000000000000000000),((-36507824053248395401927:ℚ)/92416000000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((3671394227:ℚ)/5000000000),((315549841:ℚ)/400000000),((18054182681:ℚ)/64800000000),((462749841:ℚ)/1220000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((521814257:ℚ)/2000000000),((767553550541249271365352072444549725770720123237489939:ℚ)/9307639631250000000000000000000000000000000000000000000),((-12094357576811187:ℚ)/30400000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((1955217379:ℚ)/2500000000),((9797571207:ℚ)/10000000000),((9385652137:ℚ)/40000000000),((13477571207:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2047104812186436149372864784164940377616711688989784999:ℚ)/19929037500000000000000000000000000000000000000000000000),((-6544449:ℚ)/16000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((4865122989:ℚ)/5000000000),((13607901839:ℚ)/10000000000),((21635368967:ℚ)/110400000000),((17287901839:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((5316943011237436517470545587746261449007:ℚ)/38088000000000000000000000000000000000000),((-6544449:ℚ)/16000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC20
#check @N11Formalization.C450Source24GroupedC20.bound
#print axioms N11Formalization.C450Source24GroupedC20.valid0
#print axioms N11Formalization.C450Source24GroupedC20.valid1
#print axioms N11Formalization.C450Source24GroupedC20.valid2
#print axioms N11Formalization.C450Source24GroupedC20.valid3
#print axioms N11Formalization.C450Source24GroupedC20.valid4
#print axioms N11Formalization.C450Source24GroupedC20.valid5
#print axioms N11Formalization.C450Source24GroupedC20.valid6
#print axioms N11Formalization.C450Source24GroupedC20.valid7
#print axioms N11Formalization.C450Source24GroupedC20.valid8
#print axioms N11Formalization.C450Source24GroupedC20.valid9
#print axioms N11Formalization.C450Source24GroupedC20.valid10
#print axioms N11Formalization.C450Source24GroupedC20.bound
#print axioms N11Formalization.C450Source24GroupedC20.endpoint_checks
