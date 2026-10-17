import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((9:ℚ)/16),((5:ℚ)/8),((5438045289:ℚ)/10000000000),((1153553921:ℚ)/2000000000),((66222407601:ℚ)/103000000000),((1511953921:ℚ)/1984000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7734105789:ℚ)/10000000000),((-431324518395531643861271099726349026627880949806790527127:ℚ)/1553462324428800000000000000000000000000000000000000000000),((-248055307380425717125282281:ℚ)/591462400000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((5677852791:ℚ)/10000000000),((3003752127:ℚ)/5000000000),((22793558373:ℚ)/35600000000),((3899752127:ℚ)/5150000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((727129027:ℚ)/1000000000),((-467105368187707361119403041108850878779755818820244248403:ℚ)/1690525501367187500000000000000000000000000000000000000000),((-1533295222006401900296438889:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((2958746929:ℚ)/5000000000),((6247083323:ℚ)/10000000000),((35268722361:ℚ)/55300000000),((2679694441:ℚ)/3560000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1695841357:ℚ)/2500000000),((-1111804553369948743667826646424646815782608921525758509183:ℚ)/4042234967268750000000000000000000000000000000000000000000),((-6060803048345577480059745089:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((9:ℚ)/16),((5:ℚ)/8),((6156985943:ℚ)/10000000000),((3183409763:ℚ)/5000000000),((8076985943:ℚ)/12500000000),((4079409763:ℚ)/5530000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((783028699:ℚ)/1250000000),((-3482881500061683488670245933286030144378245140860541:ℚ)/12386160424804687500000000000000000000000000000000000),((-1510194070579021604182108529:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((6276680911:ℚ)/10000000000),((3243261287:ℚ)/5000000000),((73770128199:ℚ)/114400000000),((4139261287:ℚ)/5625000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2995184253:ℚ)/5000000000),((-6379517887933278834760001843937957848991524878412261169187:ℚ)/22746766662597656250000000000000000000000000000000000000000),((-1500493656519094195422976729:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((6396344127:ℚ)/10000000000),((6606194119:ℚ)/10000000000),((74847097143:ℚ)/116300000000),((8398194119:ℚ)/11440000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5705126409:ℚ)/10000000000),((-321883275318984507394255647096901950949335945545403758523849:ℚ)/1150601232809600000000000000000000000000000000000000000000000),((-5962130748187028064809279001:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((6515977171:ℚ)/10000000000),((6725835703:ℚ)/10000000000),((25307931513:ℚ)/39400000000),((8517835703:ℚ)/11630000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5406672813:ℚ)/10000000000),((-26620025216660901854595297444198195065961623416439448087243:ℚ)/95387534255192187500000000000000000000000000000000000000000),((-5921244951563113576701114169:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((3317790759:ℚ)/5000000000),((6845448769:ℚ)/10000000000),((38500116831:ℚ)/60050000000),((8637448769:ℚ)/11820000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((5092655147:ℚ)/10000000000),((-3108682855309872949179147657976480135991343044691381951473687:ℚ)/11165539831330162500000000000000000000000000000000000000000000),((-5879317518941591179861956201:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((6755158551:ℚ)/10000000000),((6965034667:ℚ)/10000000000),((78076426959:ℚ)/122000000000),((8757034667:ℚ)/12010000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4759962623:ℚ)/10000000000),((-33573905311164993956718983452212535545788967920715514576709:ℚ)/120862052237268750000000000000000000000000000000000000000000),((-5836348716117997449444110049:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((6874709563:ℚ)/10000000000),((3602064977:ℚ)/5000000000),((79152386067:ℚ)/125800000000),((4498064977:ℚ)/6100000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((4404332321:ℚ)/10000000000),((-113986567029717418823477638839516362959435596277574746351351:ℚ)/420951514785937500000000000000000000000000000000000000000000),((-1432397697264993166520241289:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((7113738299:ℚ)/10000000000),((7443130801:ℚ)/10000000000),((9033738299:ℚ)/14400000000),((9235130801:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((899138249:ℚ)/2500000000),((-7351832014240718280149864574981229558659439454401098113:ℚ)/27239882850000000000000000000000000000000000000000000000),((-5636374197833411282734068041:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((7352676571:ℚ)/10000000000),((9352553027:ℚ)/10000000000),((83454089139:ℚ)/160000000000),((3714851009:ℚ)/4320000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((2558148057:ℚ)/10000000000),((-298751778506884161001797275159475600389094563407408247:ℚ)/1511654400000000000000000000000000000000000000000000000),((-5741219402564021:ℚ)/15200000000000000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((9261706679:ℚ)/10000000000),((6581790217:ℚ)/5000000000),((33545120037:ℚ)/73600000000),((7477790217:ℚ)/8000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-9895290024663769285103151011961034391:ℚ)/67712000000000000000000000000000000000),((-389312827:ℚ)/1024000000)⟩
theorem valid12 : Valid source29 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((553:ℚ)/800) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC26
#check @N11Formalization.C450Source29GroupedC26.bound
#print axioms N11Formalization.C450Source29GroupedC26.valid0
#print axioms N11Formalization.C450Source29GroupedC26.valid1
#print axioms N11Formalization.C450Source29GroupedC26.valid2
#print axioms N11Formalization.C450Source29GroupedC26.valid3
#print axioms N11Formalization.C450Source29GroupedC26.valid4
#print axioms N11Formalization.C450Source29GroupedC26.valid5
#print axioms N11Formalization.C450Source29GroupedC26.valid6
#print axioms N11Formalization.C450Source29GroupedC26.valid7
#print axioms N11Formalization.C450Source29GroupedC26.valid8
#print axioms N11Formalization.C450Source29GroupedC26.valid9
#print axioms N11Formalization.C450Source29GroupedC26.valid10
#print axioms N11Formalization.C450Source29GroupedC26.valid11
#print axioms N11Formalization.C450Source29GroupedC26.valid12
#print axioms N11Formalization.C450Source29GroupedC26.bound
#print axioms N11Formalization.C450Source29GroupedC26.endpoint_checks
