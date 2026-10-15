import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/8),((-1:ℚ)/16),((1238495417:ℚ)/2000000000),((6488324469:ℚ)/10000000000),((2249277:ℚ)/500000000),((1577504583:ℚ)/19840000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6184128583:ℚ)/10000000000),((75601669724211657233922820190955867:ℚ)/488095744000000000000000000000000000),((-15118328193347412761905921:ℚ)/73932800000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((6432305953:ℚ)/10000000000),((3363883811:ℚ)/5000000000),((-3883811:ℚ)/25750000000),((7647694047:ℚ)/103000000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((2808451413:ℚ)/5000000000),((1021506608598166671580989140395250245388665554810037441:ℚ)/6669476318359375000000000000000000000000000000000000000),((-398753572803105016834784401:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((266878673:ℚ)/400000000),((1711864093:ℚ)/2500000000),((-31864093:ℚ)/13350000000),((296321327:ℚ)/4272000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1248393959:ℚ)/2500000000),((18416506288637939056081410633319012891274571077518289:ℚ)/121818643200000000000000000000000000000000000000000000),((-671323326286089289930481:ℚ)/2957312000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((3395869933:ℚ)/5000000000),((3483572561:ℚ)/5000000000),((-123572561:ℚ)/27175000000),((3644130067:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1163456229:ℚ)/2500000000),((2361172959089231822758111046796023560273516210435044621:ℚ)/15678289831542968750000000000000000000000000000000000000),((-107499960903714476733259321:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((3455738659:ℚ)/5000000000),((1417366283:ℚ)/2000000000),((-73366283:ℚ)/11060000000),((3584261341:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((214472659:ℚ)/500000000),((5665451909189453625376000890775788686668980606735793781:ℚ)/37748298437500000000000000000000000000000000000000000000),((-110107542209281314078861209:ℚ)/462080000000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((7031181013:ℚ)/10000000000),((3603246047:ℚ)/5000000000),((-243246047:ℚ)/28125000000),((2349606329:ℚ)/37500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1946757779:ℚ)/5000000000),((4109604513021454451910535282730186526519745658760051221:ℚ)/27465820312500000000000000000000000000000000000000000000),((-450868204923926013380504841:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((7150852659:ℚ)/10000000000),((1465224537:ℚ)/2000000000),((-121224537:ℚ)/11440000000),((6929147341:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((345513497:ℚ)/1000000000),((7933705442613768711266801746598020206685177866395802833:ℚ)/53167400000000000000000000000000000000000000000000000000),((-1383942276086894277523067627:ℚ)/5544960000000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((1817623463:ℚ)/2500000000),((372286233:ℚ)/500000000),((-36286233:ℚ)/2907500000),((1702376537:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1477718463:ℚ)/5000000000),((1429280142569079512548450528452093392305744582284438071:ℚ)/9601060467529296875000000000000000000000000000000000000),((-29485497570300546497496641:ℚ)/115520000000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((7390106081:ℚ)/10000000000),((3842424093:ℚ)/5000000000),((-160808031:ℚ)/9850000000),((6689893919:ℚ)/118200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1177830373:ℚ)/5000000000),((384727686257641805300280158212621237198430010656884785257:ℚ)/2580313387500000000000000000000000000000000000000000000000),((-482229934390258143360922129:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((1525849827:ℚ)/2000000000),((8162806967:ℚ)/10000000000),((-1442806967:ℚ)/61000000000),((1290150173:ℚ)/24400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((849188437692358108840890966905234766580500434047608091:ℚ)/5674525000000000000000000000000000000000000000000000000),((-34668571:ℚ)/128000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((4053621737:ℚ)/5000000000),((10071812087:ℚ)/10000000000),((-3351812087:ℚ)/64800000000),((331819807:ℚ)/7200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((5648187114107746647635054363658778445885640895509961:ℚ)/36450000000000000000000000000000000000000000000000000),((-34668571:ℚ)/128000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((5008178291:ℚ)/5000000000),((13882352743:ℚ)/10000000000),((-7162352743:ℚ)/80000000000),((2031821709:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((5542791810723569587564239137156886689:ℚ)/32000000000000000000000000000000000000),((-34668571:ℚ)/128000000)⟩
theorem valid11 : Valid source23 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC15
#check @N11Formalization.C450Source23GroupedC15.bound
#print axioms N11Formalization.C450Source23GroupedC15.valid0
#print axioms N11Formalization.C450Source23GroupedC15.valid1
#print axioms N11Formalization.C450Source23GroupedC15.valid2
#print axioms N11Formalization.C450Source23GroupedC15.valid3
#print axioms N11Formalization.C450Source23GroupedC15.valid4
#print axioms N11Formalization.C450Source23GroupedC15.valid5
#print axioms N11Formalization.C450Source23GroupedC15.valid6
#print axioms N11Formalization.C450Source23GroupedC15.valid7
#print axioms N11Formalization.C450Source23GroupedC15.valid8
#print axioms N11Formalization.C450Source23GroupedC15.valid9
#print axioms N11Formalization.C450Source23GroupedC15.valid10
#print axioms N11Formalization.C450Source23GroupedC15.valid11
#print axioms N11Formalization.C450Source23GroupedC15.bound
#print axioms N11Formalization.C450Source23GroupedC15.endpoint_checks
