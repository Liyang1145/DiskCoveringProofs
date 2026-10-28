import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((153969327:ℚ)/250000000),((1331140173:ℚ)/2000000000),((83323109:ℚ)/890000000),((1779140173:ℚ)/9920000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1565054351:ℚ)/2500000000),((22978277067190989283236669704337894183:ℚ)/1933103194112000000000000000000000000000),((-1035990113962330540049291:ℚ)/27724800000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((6634216593:ℚ)/10000000000),((3387263029:ℚ)/5000000000),((10474216593:ℚ)/108700000000),((4507263029:ℚ)/26700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5096337669:ℚ)/10000000000),((4758239104031099188685704347026231693868450300388518406703231:ℚ)/421690817657756250000000000000000000000000000000000000000000000),((-1742971716827833721759804171:ℚ)/44359680000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((844133471:ℚ)/1250000000),((3446674333:ℚ)/5000000000),((1324133471:ℚ)/13825000000),((4566674333:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4765962809:ℚ)/10000000000),((80575827620435484093035237645938690992363127433608894645247:ℚ)/7191843202641485595703125000000000000000000000000000000000000),((-9189295678741413128699513:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((6871915463:ℚ)/10000000000),((3506084409:ℚ)/5000000000),((10711915463:ℚ)/112500000000),((4626084409:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2206473949:ℚ)/5000000000),((17016033375810811625513773672364571395727193402838748751:ℚ)/1528806086718750000000000000000000000000000000000000000000),((-595242787263717526512679017:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((1:ℚ)/16),((1:ℚ)/8),((3495379927:ℚ)/5000000000),((1767894503:ℚ)/2500000000),((5415379927:ℚ)/56725000000),((2327894503:ℚ)/14062500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((2015659967:ℚ)/5000000000),((987221040062080558038016803961597985438282082794717735605391:ℚ)/89482192254066467285156250000000000000000000000000000000000000),((-150593543496422012014996297:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((7050180863:ℚ)/10000000000),((3565493319:ℚ)/5000000000),((10890180863:ℚ)/114400000000),((4685493319:ℚ)/28362500000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((956779389:ℚ)/2500000000),((49353880687875436707215017998005812231915820424645904463:ℚ)/4486134212513916015625000000000000000000000000000000000000),((-605941191488292687809596217:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/16),((1:ℚ)/8),((3554800553:ℚ)/5000000000),((719039471:ℚ)/1000000000),((5474800553:ℚ)/57675000000),((85730861:ℚ)/520000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((225749277:ℚ)/625000000),((1425457502935151259451028873773586119906754465460241357:ℚ)/129922011700000000000000000000000000000000000000000000000),((-152377273300942941208164937:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((7169020603:ℚ)/10000000000),((7249802241:ℚ)/10000000000),((11009020603:ℚ)/116300000000),((9489802241:ℚ)/57675000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((422980621:ℚ)/1250000000),((236638379969459331943199618636072869345344624270528396922571:ℚ)/21624246980104253906250000000000000000000000000000000000000000),((-613077880297525498438040337:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/16),((1:ℚ)/8),((7228439373:ℚ)/10000000000),((1827302311:ℚ)/2500000000),((11068439373:ℚ)/117250000000),((2387302311:ℚ)/14537500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((196240441:ℚ)/625000000),((11526590008711662500036178920040754487554460130222491932983:ℚ)/1055929430749105834960937500000000000000000000000000000000000),((-1849942661628367607143285091:ℚ)/44359680000000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((7287857433:ℚ)/10000000000),((7368615733:ℚ)/10000000000),((3709285811:ℚ)/39400000000),((9608615733:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1437978687:ℚ)/5000000000),((133056727586036406688455250997130259897216821604753647425429:ℚ)/12218026014956665039062500000000000000000000000000000000000000),((-1860654344781364894917713531:ℚ)/44359680000000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/16),((1:ℚ)/8),((7347274799:ℚ)/10000000000),((7428021719:ℚ)/10000000000),((11187274799:ℚ)/119150000000),((9668021719:ℚ)/59100000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((2586088363:ℚ)/10000000000),((238816599268138123291677656071064548610899932497129661359580421:ℚ)/21979195875223481250000000000000000000000000000000000000000000000),((-623789564379030742058725593:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((740669149:ℚ)/1000000000),((3743713607:ℚ)/5000000000),((1124669149:ℚ)/12010000000),((4863713607:ℚ)/29787500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2260260769:ℚ)/10000000000),((161459624470934239185724221611317873434946686388003947594071:ℚ)/14891834997348546600341796875000000000000000000000000000000000),((-6273619033417540009388993:ℚ)/147865600000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((11665793:ℚ)/15625000),((7606236779:ℚ)/10000000000),((17665793:ℚ)/190625000),((9846236779:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((469965491:ℚ)/2500000000),((54626542224404990440385741942308457920753077405211420773323:ℚ)/5035918843219531250000000000000000000000000000000000000000000),((-1540368976136842559657:ℚ)/36100000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((7584937661:ℚ)/10000000000),((8081457561:ℚ)/10000000000),((11424937661:ℚ)/129600000000),((10321457561:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((125937817:ℚ)/2000000000),((25504018936468657266273165625483961471438835696249079230737:ℚ)/2326909907812500000000000000000000000000000000000000000000000),((-638084265884212591888269953:ℚ)/14786560000000000000000000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((8060234707:ℚ)/10000000000),((9982130841:ℚ)/10000000000),((11900234707:ℚ)/160000000000),((12222130841:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3608500685027463499955463195560056683863032677140967659:ℚ)/318864600000000000000000000000000000000000000000000000000),((-8850287:ℚ)/204800000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((9961140503:ℚ)/10000000000),((6891460521:ℚ)/5000000000),((13801140503:ℚ)/220800000000),((8011460521:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((981321742884232896370449161662997979499:ℚ)/76176000000000000000000000000000000000000),((-8850287:ℚ)/204800000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC18
#check @N11Formalization.C450EighthGroupedC18.bound
#print axioms N11Formalization.C450EighthGroupedC18.valid0
#print axioms N11Formalization.C450EighthGroupedC18.valid1
#print axioms N11Formalization.C450EighthGroupedC18.valid2
#print axioms N11Formalization.C450EighthGroupedC18.valid3
#print axioms N11Formalization.C450EighthGroupedC18.valid4
#print axioms N11Formalization.C450EighthGroupedC18.valid5
#print axioms N11Formalization.C450EighthGroupedC18.valid6
#print axioms N11Formalization.C450EighthGroupedC18.valid7
#print axioms N11Formalization.C450EighthGroupedC18.valid8
#print axioms N11Formalization.C450EighthGroupedC18.valid9
#print axioms N11Formalization.C450EighthGroupedC18.valid10
#print axioms N11Formalization.C450EighthGroupedC18.valid11
#print axioms N11Formalization.C450EighthGroupedC18.valid12
#print axioms N11Formalization.C450EighthGroupedC18.valid13
#print axioms N11Formalization.C450EighthGroupedC18.valid14
#print axioms N11Formalization.C450EighthGroupedC18.valid15
#print axioms N11Formalization.C450EighthGroupedC18.bound
#print axioms N11Formalization.C450EighthGroupedC18.endpoint_checks
