import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((1518532903:ℚ)/2500000000),((6616738247:ℚ)/10000000000),((176:ℚ)/1335),((21336738247:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((201495917:ℚ)/312500000),((1282899447765187539979320693947773000427831:ℚ)/8698964373504000000000000000000000000000000),((-173210742556695197077951083:ℚ)/591462400000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((6554045297:ℚ)/10000000000),((274250269:ℚ)/400000000),((352:ℚ)/2765),((287683423:ℚ)/1424000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5308552827:ℚ)/10000000000),((14836272496624703605068139531927372405838990099936474729:ℚ)/104791103961600000000000000000000000000000000000000000000),((-298836545022590975790707:ℚ)/946339840000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((3396872661:ℚ)/5000000000),((3487982103:ℚ)/5000000000),((704:ℚ)/5625),((1549711729:ℚ)/7900000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4647941421:ℚ)/10000000000),((17389009615652088422489324535524533515343878548870164379:ℚ)/124800496875000000000000000000000000000000000000000000000),((-145155497878393165987378849:ℚ)/443596800000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((6913538859:ℚ)/10000000000),((7095639509:ℚ)/10000000000),((8:ℚ)/65),((21815639509:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((214146329:ℚ)/500000000),((104397060296888871840159951518692705183829238164947384796551:ℚ)/751959228515625000000000000000000000000000000000000000000000),((-10358257104263617126522513:ℚ)/31129600000000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((703329729:ℚ)/1000000000),((1443056847:ℚ)/2000000000),((704:ℚ)/5815),((4387056847:ℚ)/22880000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3886173217:ℚ)/10000000000),((5254957782146943635384770482565605714564627690050717929449599:ℚ)/37969840682716800000000000000000000000000000000000000000000000),((-24008191106690206503825649:ℚ)/70975488000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((1430604473:ℚ)/2000000000),((7334899883:ℚ)/10000000000),((352:ℚ)/2955),((22054899883:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3446695651:ℚ)/10000000000),((6582931461099050460458698176006729199464101182971601767149393:ℚ)/47693767127596093750000000000000000000000000000000000000000000),((-203324837605757510150306243:ℚ)/591462400000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((7272715717:ℚ)/10000000000),((946756181:ℚ)/1250000000),((176:ℚ)/1525),((928918727:ℚ)/4925000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1472691439:ℚ)/5000000000),((577336586993062411643151199032494142951226301684650650751:ℚ)/4167250917919921875000000000000000000000000000000000000000),((-3223954894532845584063907:ℚ)/9241600000000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((3756006637:ℚ)/5000000000),((8052055641:ℚ)/10000000000),((44:ℚ)/405),((22772055641:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1523128927:ℚ)/10000000000),((1298557634197298551339036270419598636594311063311705103944539:ℚ)/9307639631250000000000000000000000000000000000000000000000000),((-175378504703912917:ℚ)/486400000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((3995144451:ℚ)/5000000000),((9961204749:ℚ)/10000000000),((11:ℚ)/125),((24681204749:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((185759964255189376057222371955526604579323823317333092357:ℚ)/1275458400000000000000000000000000000000000000000000000000),((-373661553:ℚ)/1024000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((9900256083:ℚ)/10000000000),((275438269:ℚ)/200000000),((22:ℚ)/345),((569838269:ℚ)/3200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((3286679589441415614389503334533536677:ℚ)/19501056000000000000000000000000000000),((-373661553:ℚ)/1024000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
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
private theorem node5_7 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_10
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_10
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9]
theorem packet_count : packets.length = 10 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC17
#check @N11Formalization.C450Source24GroupedC17.bound
#print axioms N11Formalization.C450Source24GroupedC17.valid0
#print axioms N11Formalization.C450Source24GroupedC17.valid1
#print axioms N11Formalization.C450Source24GroupedC17.valid2
#print axioms N11Formalization.C450Source24GroupedC17.valid3
#print axioms N11Formalization.C450Source24GroupedC17.valid4
#print axioms N11Formalization.C450Source24GroupedC17.valid5
#print axioms N11Formalization.C450Source24GroupedC17.valid6
#print axioms N11Formalization.C450Source24GroupedC17.valid7
#print axioms N11Formalization.C450Source24GroupedC17.valid8
#print axioms N11Formalization.C450Source24GroupedC17.valid9
#print axioms N11Formalization.C450Source24GroupedC17.bound
#print axioms N11Formalization.C450Source24GroupedC17.endpoint_checks
