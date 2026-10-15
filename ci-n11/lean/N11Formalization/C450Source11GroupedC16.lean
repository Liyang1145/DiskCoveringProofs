import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC16
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((-1:ℚ)/16),(0:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/16),(0:ℚ),((6187083317:ℚ)/10000000000),((1337610221:ℚ)/2000000000),((-185610221:ℚ)/19840000000),((2:ℚ)/31),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((309817991:ℚ)/500000000),((17170710653528167:ℚ)/595820000000000000),((-10672892686157812657937343:ℚ)/295731200000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((33315021:ℚ)/50000000),((6807010329:ℚ)/10000000000),((-3921387:ℚ)/400000000),((16:ℚ)/267),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((15681711:ℚ)/31250000),((2494091277324984650560870966121:ℚ)/89222639062500000000000000000000),((-893007718461134272738950629:ℚ)/22179840000000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((3390982123:ℚ)/5000000000),((1385192469:ℚ)/2000000000),((-233192469:ℚ)/21740000000),((64:ℚ)/1087),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((468240599:ℚ)/1000000000),((2616453936950711439419549243069:ℚ)/94069738989257812500000000000000),((-36634817304723776972303309:ℚ)/887193600000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/16),(0:ℚ),((107826829:ℚ)/156250000),((7044907521:ℚ)/10000000000),((-1284907521:ℚ)/110600000000),((32:ℚ)/553),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2161370407:ℚ)/5000000000),((522552135090164816043292944773:ℚ)/18874149218750000000000000000000),((-938725588184494907457077429:ℚ)/22179840000000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/16),(0:ℚ),((7019862999:ℚ)/10000000000),((7104377651:ℚ)/10000000000),((-1344377651:ℚ)/112500000000),((64:ℚ)/1125),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((491570267:ℚ)/1250000000),((15319412063641860726066245114491:ℚ)/556182861328125000000000000000000),((-320586057977250191930183423:ℚ)/7393280000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/16),(0:ℚ),((55307293:ℚ)/78125000),((3581923099:ℚ)/5000000000),((-701923099:ℚ)/56725000000),((128:ℚ)/2269),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((930763157:ℚ)/2500000000),((2508776568371214469636278106307:ℚ)/91262743039062500000000000000000),((-81098396561019692808361423:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/16),(0:ℚ),((3569401209:ℚ)/5000000000),((18058283:ℚ)/25000000),((-3658283:ℚ)/286000000),((8:ℚ)/143),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3501650419:ℚ)/10000000000),((188048621917438747625908850657:ℚ)/6853610156250000000000000000000),((-2051253117572480262047:ℚ)/46208000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((3599134891:ℚ)/5000000000),((910347337:ℚ)/1250000000),((-190347337:ℚ)/14418750000),((128:ℚ)/2307),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3265933261:ℚ)/10000000000),((875753773768588753480745686073:ℚ)/31975074070312500000000000000000),((-5187606224157113779792087:ℚ)/115520000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-1:ℚ)/16),(0:ℚ),((3628867817:ℚ)/5000000000),((3671121361:ℚ)/5000000000),((-791121361:ℚ)/58150000000),((64:ℚ)/1163),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((602507601:ℚ)/2000000000),((12600481057547034903494563849649:ℚ)/460850902441406250000000000000000),((-83953121830093894805997383:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((731720001:ℚ)/1000000000),((3700852657:ℚ)/5000000000),((-820852657:ℚ)/58625000000),((128:ℚ)/2345),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((136827653:ℚ)/500000000),((17187676144216508808060018272519:ℚ)/629649102783203125000000000000000),((-84904392019028413216577927:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((3688331473:ℚ)/5000000000),((7520626331:ℚ)/10000000000),((-1760626331:ℚ)/118200000000),((32:ℚ)/591),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((243028889:ℚ)/1000000000),((13197917171447468445494393360729:ℚ)/483808760156250000000000000000000),((-343357330903788512835229903:ℚ)/7393280000000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-1:ℚ)/16),(0:ℚ),((1499116927:ℚ)/2000000000),((7639542011:ℚ)/10000000000),((-1879542011:ℚ)/120100000000),((64:ℚ)/1201),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1659544457:ℚ)/10000000000),((18406464399669667588756835704691:ℚ)/676688906640625000000000000000000),((-4618516089416487:ℚ)/97280000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/16),(0:ℚ),((3807250483:ℚ)/5000000000),((4057578029:ℚ)/5000000000),((-1177578029:ℚ)/61000000000),((16:ℚ)/305),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((302253654682247911021494196219:ℚ)/11083056640625000000000000000000),((-24778429:ℚ)/512000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/16),(0:ℚ),((4045058713:ℚ)/5000000000),((400681123:ℚ)/400000000),((-170281123:ℚ)/5184000000),((4:ℚ)/81),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((17181909484935809084706301817:ℚ)/622782421875000000000000000000),((-24778429:ℚ)/512000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/16),(0:ℚ),((1998399359:ℚ)/2000000000),((13819224337:ℚ)/10000000000),((-8059224337:ℚ)/160000000000),((1:ℚ)/25),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((151028653635859:ℚ)/5000000000000000),((-24778429:ℚ)/512000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((2307:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC16
#check @N11Formalization.C450Source11GroupedC16.bound
#print axioms N11Formalization.C450Source11GroupedC16.valid0
#print axioms N11Formalization.C450Source11GroupedC16.valid1
#print axioms N11Formalization.C450Source11GroupedC16.valid2
#print axioms N11Formalization.C450Source11GroupedC16.valid3
#print axioms N11Formalization.C450Source11GroupedC16.valid4
#print axioms N11Formalization.C450Source11GroupedC16.valid5
#print axioms N11Formalization.C450Source11GroupedC16.valid6
#print axioms N11Formalization.C450Source11GroupedC16.valid7
#print axioms N11Formalization.C450Source11GroupedC16.valid8
#print axioms N11Formalization.C450Source11GroupedC16.valid9
#print axioms N11Formalization.C450Source11GroupedC16.valid10
#print axioms N11Formalization.C450Source11GroupedC16.valid11
#print axioms N11Formalization.C450Source11GroupedC16.valid12
#print axioms N11Formalization.C450Source11GroupedC16.valid13
#print axioms N11Formalization.C450Source11GroupedC16.valid14
#print axioms N11Formalization.C450Source11GroupedC16.bound
#print axioms N11Formalization.C450Source11GroupedC16.endpoint_checks
