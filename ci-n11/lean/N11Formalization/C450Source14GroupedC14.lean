import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((780210327:ℚ)/1250000000),((6514704417:ℚ)/10000000000),((-11864113251:ℚ)/99200000000),((-260210327:ℚ)/6437500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6071558381:ℚ)/10000000000),((6918551003524481365298027925098605843788816588899702861:ℚ)/155065324401855468750000000000000000000000000000000000000),((-352167588764983851194893:ℚ)/28880000000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((809982537:ℚ)/1250000000),((1688232177:ℚ)/2500000000),((-3144696531:ℚ)/25750000000),((-289982537:ℚ)/6675000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5498303251:ℚ)/10000000000),((2114895987302295012546842332207281579911907372417014201:ℚ)/47864228247070312500000000000000000000000000000000000000),((-445339901351111782311373:ℚ)/28880000000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((6717989559:ℚ)/10000000000),((343601089:ℚ)/500000000),((-215601089:ℚ)/1780000000),((-2557989559:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4865612691:ℚ)/10000000000),((3888372780117858018295284101067618988362585619282457723409:ℚ)/89303538880468750000000000000000000000000000000000000000000),((-34464694333746861804608077:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((6837037629:ℚ)/10000000000),((1398220603:ℚ)/2000000000),((-2658661809:ℚ)/21740000000),((-382433947:ℚ)/7900000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2259601089:ℚ)/5000000000),((6811777598659637441156320917042053187332140009494667873:ℚ)/157011736230468750000000000000000000000000000000000000000),((-37446171628090476175253797:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((6956075421:ℚ)/10000000000),((1410127877:ℚ)/2000000000),((-2694383631:ℚ)/22120000000),((-2796075421:ℚ)/55775000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((4146110261:ℚ)/10000000000),((1615590334616456847529876953410698342105571087406142306483:ℚ)/37480372877337646484375000000000000000000000000000000000000),((-40427672576802957325248997:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((1753897657:ℚ)/2500000000),((7110173017:ℚ)/10000000000),((-13650519051:ℚ)/111550000000),((-713897657:ℚ)/14062500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((98680159:ℚ)/250000000),((19557308420719207991227428307702924513286924440859564491:ℚ)/454410631209611892700195312500000000000000000000000000000),((-7257346959513656230053:ℚ)/320000000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((3537551729:ℚ)/5000000000),((7169703983:ℚ)/10000000000),((-4609703983:ℚ)/37500000000),((-1457551729:ℚ)/28362500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((747664701:ℚ)/2000000000),((15320627874459167720485404965247120645974952894218839:ℚ)/356495089996337890625000000000000000000000000000000000),((-10852302552087188170586397:ℚ)/462080000000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((1783653493:ℚ)/2500000000),((1807308087:ℚ)/2500000000),((-3501924261:ℚ)/28362500000),((-67604863:ℚ)/1300000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1758840079:ℚ)/5000000000),((1337083032970317096259923753805378368821040909778645477:ℚ)/31156206250000000000000000000000000000000000000000000000),((-2806249787944658349102933:ℚ)/115520000000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((1798530557:ℚ)/2500000000),((3644379089:ℚ)/5000000000),((-7093137267:ℚ)/57200000000),((-252843519:ℚ)/4806250000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3282901357:ℚ)/10000000000),((166122098849834023711836496732985750024541035885727:ℚ)/3876101677834987640380859375000000000000000000000000),((-8031647624531988908253:ℚ)/320000000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((3626814141:ℚ)/5000000000),((3674140767:ℚ)/5000000000),((-2394140767:ℚ)/19225000000),((-1546814141:ℚ)/29075000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3030698917:ℚ)/10000000000),((5056420029988536122320259284017177547377094663620500712819:ℚ)/118131447992480468750000000000000000000000000000000000000000),((-11970402954977655600675877:ℚ)/462080000000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((7313132187:ℚ)/10000000000),((1493464213:ℚ)/2000000000),((-2944392639:ℚ)/23260000000),((-3153132187:ℚ)/59100000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2756288867:ℚ)/10000000000),((595721892808711072360470608812037759652295397495220027613:ℚ)/13893076248437500000000000000000000000000000000000000000000),((-49372443349071117991243573:ℚ)/1848320000000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((7432133763:ℚ)/10000000000),((7705372981:ℚ)/10000000000),((-5145372981:ℚ)/39400000000),((-3272133763:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((263210087:ℚ)/1250000000),((36075940259277892466653049691365956785757885157315691963323:ℚ)/838411068750000000000000000000000000000000000000000000000000),((-52354160879801801664855973:ℚ)/1848320000000000000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((3835056667:ℚ)/5000000000),((511336213:ℚ)/625000000),((-1054008639:ℚ)/7625000000),((-585018889:ℚ)/10800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((6935616546542905147655206371993192595381441643728811977:ℚ)/160088400000000000000000000000000000000000000000000000000),((-3916947:ℚ)/128000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((4072993939:ℚ)/5000000000),((2521111699:ℚ)/2500000000),((-209012411:ℚ)/1200000000),((-1992993939:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((18220602963232246976158151286918416657826331202601990301:ℚ)/400000000000000000000000000000000000000000000000000000000),((-3916947:ℚ)/128000000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((251216339:ℚ)/250000000),((13888044091:ℚ)/10000000000),((-33984132273:ℚ)/160000000000),((-49072113:ℚ)/920000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((61409711821606346007395779524833967236174720880303:ℚ)/1216700000000000000000000000000000000000000000000000),((-3916947:ℚ)/128000000)⟩
theorem valid14 : Valid source14 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source14 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2269:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source14 nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC14
#check @N11Formalization.C450Source14GroupedC14.bound
#print axioms N11Formalization.C450Source14GroupedC14.valid0
#print axioms N11Formalization.C450Source14GroupedC14.valid1
#print axioms N11Formalization.C450Source14GroupedC14.valid2
#print axioms N11Formalization.C450Source14GroupedC14.valid3
#print axioms N11Formalization.C450Source14GroupedC14.valid4
#print axioms N11Formalization.C450Source14GroupedC14.valid5
#print axioms N11Formalization.C450Source14GroupedC14.valid6
#print axioms N11Formalization.C450Source14GroupedC14.valid7
#print axioms N11Formalization.C450Source14GroupedC14.valid8
#print axioms N11Formalization.C450Source14GroupedC14.valid9
#print axioms N11Formalization.C450Source14GroupedC14.valid10
#print axioms N11Formalization.C450Source14GroupedC14.valid11
#print axioms N11Formalization.C450Source14GroupedC14.valid12
#print axioms N11Formalization.C450Source14GroupedC14.valid13
#print axioms N11Formalization.C450Source14GroupedC14.valid14
#print axioms N11Formalization.C450Source14GroupedC14.bound
#print axioms N11Formalization.C450Source14GroupedC14.endpoint_checks
