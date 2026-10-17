import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC23
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((3:ℚ)/8),((7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/8),((7:ℚ)/16),((5764294673:ℚ)/10000000000),((3157211527:ℚ)/5000000000),((8004294673:ℚ)/17800000000),((29140480689:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7098497197:ℚ)/10000000000),((46059267975045225297973:ℚ)/4950625000000000000000000),((-167031076722359776389981609:ℚ)/462080000000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((3121464769:ℚ)/5000000000),((3276749601:ℚ)/5000000000),((12724394307:ℚ)/27650000000),((29977247207:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6068682081:ℚ)/10000000000),((-153271005512286287258938517858929:ℚ)/119456640625000000000000000000000000),((-515357105801551259535006763:ℚ)/1386240000000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((3:ℚ)/8),((7:ℚ)/16),((6482057683:ℚ)/10000000000),((1358493933:ℚ)/2000000000),((26166173049:ℚ)/57200000000),((12325457531:ℚ)/22120000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1098553523:ℚ)/2000000000),((-71247336039093284553838696444179:ℚ)/39325000000000000000000000000000000),((-83211179087115186553556707:ℚ)/221798400000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((3360538311:ℚ)/5000000000),((6911918541:ℚ)/10000000000),((13441614933:ℚ)/29075000000),((5678493617:ℚ)/10400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4856918589:ℚ)/10000000000),((-399126053973934650509610027624401:ℚ)/66043408203125000000000000000000000),((-2108183356593726964786612003:ℚ)/5544960000000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((427534283:ℚ)/625000000),((7031344757:ℚ)/10000000000),((567534283:ℚ)/1231250000),((63299413299:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((901722407:ℚ)/2000000000),((-5745468681717385418825148773879:ℚ)/947485351562500000000000000000000),((-705727417571643800194369329:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((6959997019:ℚ)/10000000000),((35753747:ℚ)/50000000),((27599991057:ℚ)/60050000000),((320676229:ℚ)/591000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2066641161:ℚ)/5000000000),((-3407789855065529022336497337147589:ℚ)/563437890625000000000000000000000000),((-17716771772060789106489:ℚ)/46208000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/8),((7:ℚ)/16),((7079423221:ℚ)/10000000000),((454383343:ℚ)/625000000),((27958269663:ℚ)/61000000000),((4060683401:ℚ)/7506250000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1861364047:ℚ)/5000000000),((-3487255117854346120762825841167569:ℚ)/581406250000000000000000000000000000),((-2779524240521051140944179:ℚ)/7220000000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((3599414093:ℚ)/5000000000),((7508843767:ℚ)/10000000000),((14158242279:ℚ)/31450000000),((66641906369:ℚ)/122000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1631821137:ℚ)/5000000000),((-181160745375488277570073841164149:ℚ)/77273632812500000000000000000000000),((-710926517162604842555223369:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/8),((7:ℚ)/16),((7437578297:ℚ)/10000000000),((7747482561:ℚ)/10000000000),((9677578297:ℚ)/21600000000),((68312377927:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((517781753:ℚ)/2500000000),((-2002391395046346886767310076537:ℚ)/900000000000000000000000000000000),((-189663045960375243:ℚ)/486400000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/8),((7:ℚ)/16),((959531819:ℚ)/1250000000),((9654635151:ℚ)/10000000000),((3718595457:ℚ)/10000000000),((81662446057:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((134310148979233976936480667886823:ℚ)/3906250000000000000000000000000000),((-50499073:ℚ)/128000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/8),((7:ℚ)/16),((4791821041:ℚ)/5000000000),((13463012377:ℚ)/10000000000),((5911821041:ℚ)/18400000000),((108321086639:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((383812445678396930543597:ℚ)/5290000000000000000000000),((-50499073:ℚ)/128000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source23 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source23 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC23
#check @N11Formalization.C450Source23GroupedC23.bound
#print axioms N11Formalization.C450Source23GroupedC23.valid0
#print axioms N11Formalization.C450Source23GroupedC23.valid1
#print axioms N11Formalization.C450Source23GroupedC23.valid2
#print axioms N11Formalization.C450Source23GroupedC23.valid3
#print axioms N11Formalization.C450Source23GroupedC23.valid4
#print axioms N11Formalization.C450Source23GroupedC23.valid5
#print axioms N11Formalization.C450Source23GroupedC23.valid6
#print axioms N11Formalization.C450Source23GroupedC23.valid7
#print axioms N11Formalization.C450Source23GroupedC23.valid8
#print axioms N11Formalization.C450Source23GroupedC23.valid9
#print axioms N11Formalization.C450Source23GroupedC23.valid10
#print axioms N11Formalization.C450Source23GroupedC23.bound
#print axioms N11Formalization.C450Source23GroupedC23.endpoint_checks
