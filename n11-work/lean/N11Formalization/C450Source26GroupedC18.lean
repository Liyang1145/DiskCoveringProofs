import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/16),((1:ℚ)/8),((2997550039:ℚ)/5000000000),((788224967:ℚ)/1250000000),((10677550039:ℚ)/51500000000),((1788224967:ℚ)/6200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6618949997:ℚ)/10000000000),((73081929928990742964144657804766227491:ℚ)/632105438000000000000000000000000000000),((-194797083673963992905691:ℚ)/577600000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((1558896047:ℚ)/2500000000),((6545878067:ℚ)/10000000000),((5398896047:ℚ)/26700000000),((14545878067:ℚ)/51500000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((608560863:ℚ)/1000000000),((26996099872767257320308868475895340704326711199973186150357:ℚ)/237730148629760742187500000000000000000000000000000000000000),((-12867315118221893800508291:ℚ)/36966400000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((1295170443:ℚ)/2000000000),((3332924289:ℚ)/5000000000),((4367170443:ℚ)/21740000000),((7332924289:ℚ)/26700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5508387513:ℚ)/10000000000),((46349652616060297008737697568810377482101791229982626834807717:ℚ)/421690817657756250000000000000000000000000000000000000000000000),((-9971013823523274877209697:ℚ)/27724800000000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((164897811:ℚ)/250000000),((6785776529:ℚ)/10000000000),((78413973:ℚ)/395000000),((14785776529:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2599355547:ℚ)/5000000000),((128332646657557814145571808064864773276332982371189192917997:ℚ)/1174178482063916015625000000000000000000000000000000000000000),((-13493199038380180581383979:ℚ)/36966400000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((6715926927:ℚ)/10000000000),((6905664117:ℚ)/10000000000),((7358642309:ℚ)/37500000000),((14905664117:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((487141373:ℚ)/1000000000),((147797405329202110735927757947403844399273143919368882861:ℚ)/1358938743750000000000000000000000000000000000000000000000),((-41073328462956087602317273:ℚ)/110899200000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((170897451:ℚ)/250000000),((7025513393:ℚ)/10000000000),((554897451:ℚ)/2860000000),((15025513393:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4522634627:ℚ)/10000000000),((2463474024466109227130111648980858661360191505313452564865743:ℚ)/22746766662597656250000000000000000000000000000000000000000000),((-13888420940303552503511531:ℚ)/36966400000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((3477913993:ℚ)/5000000000),((3572663133:ℚ)/5000000000),((11157913993:ℚ)/58150000000),((7572663133:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((518364799:ℚ)/1250000000),((1455051264243246997426909363405032992064308172390449142423971:ℚ)/13483608196987500000000000000000000000000000000000000000000000),((-10563853195160067559519273:ℚ)/27724800000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((353785941:ℚ)/500000000),((1816276131:ℚ)/2500000000),((373928647:ℚ)/1970000000),((3816276131:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1868052843:ℚ)/5000000000),((60134964684649988674566576580823262228052533135041886256847:ℚ)/558911333526516723632812500000000000000000000000000000000000),((-2677736878950198354907177:ℚ)/6931200000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((1439114493:ℚ)/2000000000),((750456377:ℚ)/1000000000),((4511114493:ℚ)/24400000000),((1550456377:ℚ)/5910000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3276977909:ℚ)/10000000000),((1569990134052873702030098396421417567997968519425562659101:ℚ)/14402019172331250000000000000000000000000000000000000000000),((-144441571249984009391451:ℚ)/369664000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((371758763:ℚ)/500000000),((199578343:ℚ)/250000000),((1139758763:ℚ)/6480000000),((399578343:ℚ)/1525000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((2086447383:ℚ)/10000000000),((4058536425553921114710980687919267314922009980296981313:ℚ)/36357967309570312500000000000000000000000000000000000000),((-611549814366323:ℚ)/1520000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((3957003233:ℚ)/5000000000),((154593659:ℚ)/156250000),((11637003233:ℚ)/80000000000),((279593659:ℚ)/1012500000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((9737216131461880777541378022432429706069495784931583:ℚ)/77847802734375000000000000000000000000000000000000000),((-26291521:ℚ)/64000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((9825659523:ℚ)/10000000000),((13706698953:ℚ)/10000000000),((8395219841:ℚ)/73600000000),((21706698953:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((10649521000288934444895752726112253894509:ℚ)/67712000000000000000000000000000000000000),((-26291521:ℚ)/64000000)⟩
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
end N11Formalization.C450Source26GroupedC18
#check @N11Formalization.C450Source26GroupedC18.bound
#print axioms N11Formalization.C450Source26GroupedC18.valid0
#print axioms N11Formalization.C450Source26GroupedC18.valid1
#print axioms N11Formalization.C450Source26GroupedC18.valid2
#print axioms N11Formalization.C450Source26GroupedC18.valid3
#print axioms N11Formalization.C450Source26GroupedC18.valid4
#print axioms N11Formalization.C450Source26GroupedC18.valid5
#print axioms N11Formalization.C450Source26GroupedC18.valid6
#print axioms N11Formalization.C450Source26GroupedC18.valid7
#print axioms N11Formalization.C450Source26GroupedC18.valid8
#print axioms N11Formalization.C450Source26GroupedC18.valid9
#print axioms N11Formalization.C450Source26GroupedC18.valid10
#print axioms N11Formalization.C450Source26GroupedC18.valid11
#print axioms N11Formalization.C450Source26GroupedC18.bound
#print axioms N11Formalization.C450Source26GroupedC18.endpoint_checks
