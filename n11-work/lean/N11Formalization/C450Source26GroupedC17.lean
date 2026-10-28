import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),(0:ℚ),((1:ℚ)/16),((1211328521:ℚ)/2000000000),((6365516969:ℚ)/10000000000),((384:ℚ)/2575),((22365516969:ℚ)/99200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3243029969:ℚ)/5000000000),((347466126238489910327322994376792252917613:ℚ)/2589103874048000000000000000000000000000000),((-92324354156742777489831627:ℚ)/295731200000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((6297162921:ℚ)/10000000000),((6605605577:ℚ)/10000000000),((64:ℚ)/445),((22605605577:ℚ)/103000000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5942403177:ℚ)/10000000000),((27925513760516367978697302285316188392404210520235450098543:ℚ)/211315687670898437500000000000000000000000000000000000000000),((-95836024251717644423838603:ℚ)/295731200000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((3268732243:ℚ)/5000000000),((6725580949:ℚ)/10000000000),((768:ℚ)/5435),((22725580949:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5351489177:ℚ)/10000000000),((3487465693174215991261286155468341656519435127813954881757696257:ℚ)/26988212330096400000000000000000000000000000000000000000000000000),((-99457031072665936100783107:ℚ)/295731200000000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((6657540571:ℚ)/10000000000),((1711378397:ℚ)/2500000000),((384:ℚ)/2765),((5711378397:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2516536301:ℚ)/5000000000),((308255342009828082593320271786666244121305753563872448116107:ℚ)/2397281067547161865234375000000000000000000000000000000000000),((-6325297098560216348797363:ℚ)/18483200000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((1355514071:ℚ)/2000000000),((3482702851:ℚ)/5000000000),((256:ℚ)/1875),((145350669:ℚ)/700000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((939039991:ℚ)/2000000000),((352881722143390680208235697242360693557169460573173:ℚ)/2756250000000000000000000000000000000000000000000000),((-25737414099668066808936307:ℚ)/73932800000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((3448778117:ℚ)/5000000000),((1771314837:ℚ)/2500000000),((96:ℚ)/715),((5771314837:ℚ)/28125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4333284381:ℚ)/10000000000),((362666867841265798811786344219985414016693897321731113306547:ℚ)/2843345832824707031250000000000000000000000000000000000000000),((-19629708155489783875210249:ℚ)/55449600000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((7017500439:ℚ)/10000000000),((3602538223:ℚ)/5000000000),((768:ℚ)/5815),((11602538223:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3940666557:ℚ)/10000000000),((4571470027384355741251706591952833793102509010960380311404387:ℚ)/35956288525300000000000000000000000000000000000000000000000000),((-26607787397917552985022203:ℚ)/73932800000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((7137405053:ℚ)/10000000000),((732485879:ℚ)/1000000000),((128:ℚ)/985),((2332485879:ℚ)/11630000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((219187883:ℚ)/625000000),((12094776312523906398886108110232668406677502344280273581721:ℚ)/95387534255192187500000000000000000000000000000000000000000),((-1081678071050558924293387:ℚ)/2957312000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((7257272023:ℚ)/10000000000),((1512865163:ℚ)/2000000000),((192:ℚ)/1525),((4712865163:ℚ)/23640000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((7536483:ℚ)/25000000),((117575327103810319130164121612487974675133662828513225299759:ℚ)/921729227029200000000000000000000000000000000000000000000000),((-4390721910579121477910083:ℚ)/11829248000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((7496900189:ℚ)/10000000000),((2010727481:ℚ)/2500000000),((16:ℚ)/135),((6010727481:ℚ)/30500000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((824516457:ℚ)/5000000000),((4168511868990188246999298147052090749006549236423553289591:ℚ)/32318193164062500000000000000000000000000000000000000000000),((-46651870710335173:ℚ)/121600000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((1595155513:ℚ)/2000000000),((4976906671:ℚ)/5000000000),((12:ℚ)/125),((480626173:ℚ)/2400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2219415360783345827870681891396335569924315193301281:ℚ)/16200000000000000000000000000000000000000000000000000),((-199207049:ℚ)/512000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((9887570663:ℚ)/10000000000),((6883284101:ℚ)/5000000000),((8:ℚ)/115),((14883284101:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((11006225437836887780271291604800519539617:ℚ)/67712000000000000000000000000000000000000),((-199207049:ℚ)/512000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC17
#check @N11Formalization.C450Source26GroupedC17.bound
#print axioms N11Formalization.C450Source26GroupedC17.valid0
#print axioms N11Formalization.C450Source26GroupedC17.valid1
#print axioms N11Formalization.C450Source26GroupedC17.valid2
#print axioms N11Formalization.C450Source26GroupedC17.valid3
#print axioms N11Formalization.C450Source26GroupedC17.valid4
#print axioms N11Formalization.C450Source26GroupedC17.valid5
#print axioms N11Formalization.C450Source26GroupedC17.valid6
#print axioms N11Formalization.C450Source26GroupedC17.valid7
#print axioms N11Formalization.C450Source26GroupedC17.valid8
#print axioms N11Formalization.C450Source26GroupedC17.valid9
#print axioms N11Formalization.C450Source26GroupedC17.valid10
#print axioms N11Formalization.C450Source26GroupedC17.valid11
#print axioms N11Formalization.C450Source26GroupedC17.bound
#print axioms N11Formalization.C450Source26GroupedC17.endpoint_checks
