import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/16),((1:ℚ)/4),((5790155989:ℚ)/10000000000),((3059179629:ℚ)/5000000000),((35930467967:ℚ)/103000000000),((5459179629:ℚ)/12400000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((440382791:ℚ)/625000000),((-1276940703829912105754803525316381001294071422137319448501:ℚ)/6829543750000000000000000000000000000000000000000000000000),((-18634238437147898271881191:ℚ)/57760000000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((6031777493:ℚ)/10000000000),((3179765291:ℚ)/5000000000),((36655332479:ℚ)/106800000000),((5579765291:ℚ)/12875000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((654002889:ℚ)/1000000000),((-38612024151775451343079177831887133759773261708920013277:ℚ)/211490700000000000000000000000000000000000000000000000000),((-18837301394674795326430231:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((3136549291:ℚ)/5000000000),((129600357:ℚ)/200000000),((18689647873:ℚ)/54350000000),((75200119:ℚ)/178000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5998723089:ℚ)/10000000000),((-183098604782850556890087566702042020058392329991326347779:ℚ)/1003410549218750000000000000000000000000000000000000000000),((-30719981645922303633399:ℚ)/92416000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((3196828313:ℚ)/5000000000),((6600444157:ℚ)/10000000000),((18870484939:ℚ)/55300000000),((11400444157:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((5711670793:ℚ)/10000000000),((-425833772803509916541098633170512137828496886287857351:ℚ)/2359268652343750000000000000000000000000000000000000000),((-77172906069365793122886599:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((3257075587:ℚ)/5000000000),((168020317:ℚ)/250000000),((19051226761:ℚ)/56250000000),((288020317:ℚ)/691250000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5411338941:ℚ)/10000000000),((-28743462249746330419501889050850595813938577725780441:ℚ)/160932540893554687500000000000000000000000000000000000),((-48458075735908294128439:ℚ)/144400000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((3317292767:ℚ)/5000000000),((3420563187:ℚ)/5000000000),((19231878301:ℚ)/57200000000),((646729243:ℚ)/1562500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2547671259:ℚ)/5000000000),((-206806601993964749958980090165893015332228585742635185287:ℚ)/1169682800000000000000000000000000000000000000000000000000),((-19470007298515531868538919:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((675496279:ℚ)/1000000000),((1392277599:ℚ)/2000000000),((3882488837:ℚ)/11630000000),((2352277599:ℚ)/5720000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4760524719:ℚ)/10000000000),((-1721384772960979363778249758602630816043152549329645519:ℚ)/9831485918750000000000000000000000000000000000000000000),((-3128570314300278872206351:ℚ)/9241600000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((1375057163:ℚ)/2000000000),((3540800059:ℚ)/5000000000),((7837171489:ℚ)/23640000000),((5940800059:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((880510699:ℚ)/2000000000),((-397828495986926096982665159666004632915876395384463227:ℚ)/2293611900000000000000000000000000000000000000000000000),((-19633908249651645358159031:ℚ)/57760000000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((6995557293:ℚ)/10000000000),((7321885339:ℚ)/10000000000),((39546671879:ℚ)/122000000000),((12121885339:ℚ)/29550000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((401519871:ℚ)/1000000000),((-1914559457248548368812877047401992472773125409459113966613:ℚ)/11349050000000000000000000000000000000000000000000000000000),((-78079267796142853772532471:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((3617977739:ℚ)/5000000000),((390097899:ℚ)/500000000),((20133933217:ℚ)/64800000000),((630097899:ℚ)/1525000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((310766689:ℚ)/1000000000),((-373916890410184576816427324602617658378747455690282059:ℚ)/2332800000000000000000000000000000000000000000000000000),((-542801900579723:ℚ)/1600000000000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((7716233527:ℚ)/10000000000),((242934331:ℚ)/250000000),((41708700581:ℚ)/160000000000),((362934331:ℚ)/810000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-3366551790810653860868547208809210676034506698565929272687:ℚ)/25600000000000000000000000000000000000000000000000000000000),((-5650439:ℚ)/16000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((4816135317:ℚ)/5000000000),((1691922491:ℚ)/1250000000),((23728405951:ℚ)/110400000000),((2291922491:ℚ)/5000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-24385809021786374430168886552919649267574597790582185013:ℚ)/233606400000000000000000000000000000000000000000000000000),((-5650439:ℚ)/16000000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC20
#check @N11Formalization.C450Source31GroupedC20.bound
#print axioms N11Formalization.C450Source31GroupedC20.valid0
#print axioms N11Formalization.C450Source31GroupedC20.valid1
#print axioms N11Formalization.C450Source31GroupedC20.valid2
#print axioms N11Formalization.C450Source31GroupedC20.valid3
#print axioms N11Formalization.C450Source31GroupedC20.valid4
#print axioms N11Formalization.C450Source31GroupedC20.valid5
#print axioms N11Formalization.C450Source31GroupedC20.valid6
#print axioms N11Formalization.C450Source31GroupedC20.valid7
#print axioms N11Formalization.C450Source31GroupedC20.valid8
#print axioms N11Formalization.C450Source31GroupedC20.valid9
#print axioms N11Formalization.C450Source31GroupedC20.valid10
#print axioms N11Formalization.C450Source31GroupedC20.valid11
#print axioms N11Formalization.C450Source31GroupedC20.bound
#print axioms N11Formalization.C450Source31GroupedC20.endpoint_checks
