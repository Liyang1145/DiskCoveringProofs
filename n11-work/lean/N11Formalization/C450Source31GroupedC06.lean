import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((3429258263:ℚ)/5000000000),((177084313:ℚ)/250000000),((-1483927443:ℚ)/2480000000),((-2469258263:ℚ)/5055000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4454047007:ℚ)/10000000000),((44125821991018994904925283:ℚ)/132023962500000000000000000),((4579554427207869510072209:ℚ)/10240000000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((3489264563:ℚ)/5000000000),((7143314929:ℚ)/10000000000),((-20005488073:ℚ)/33700000000),((-2529264563:ℚ)/5102500000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((4072146849:ℚ)/10000000000),((3627022132950504591211393302242052119:ℚ)/10967457007812500000000000000000000000),((1639236626057427647552327249:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((7038517521:ℚ)/10000000000),((288129869:ℚ)/400000000),((-2427028559:ℚ)/4082000000),((-5118517521:ℚ)/10300000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((3868005271:ℚ)/10000000000),((71574817850383331033952743463041943199:ℚ)/216529690000000000000000000000000000000),((6528653664735548223923908361:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((1774623607:ℚ)/2500000000),((3631584101:ℚ)/5000000000),((-30667425111:ℚ)/51500000000),((-1294623607:ℚ)/2598750000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((3653117841:ℚ)/10000000000),((23941584442292416343882512312572379:ℚ)/72459443847656250000000000000000000),((406258891209114097647174329:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((894807521:ℚ)/1250000000),((7323079647:ℚ)/10000000000),((-61993876117:ℚ)/103950000000),((-654807521:ℚ)/1311250000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3425456999:ℚ)/10000000000),((11806317254297580545609245369645472801:ℚ)/35745838734375000000000000000000000000),((101115816599401464339688361:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7218415051:ℚ)/10000000000),((3691490667:ℚ)/5000000000),((-31326397337:ℚ)/52450000000),((-5298415051:ℚ)/10585000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((3182276339:ℚ)/10000000000),((2567221802344520778004983372665325514765325057275483384633:ℚ)/7775495826591406250000000000000000000000000000000000000000),((6442463648598576263434114721:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((454897461:ℚ)/625000000),((930359191:ℚ)/1250000000),((-7913951101:ℚ)/13231250000),((-111632487:ℚ)/222500000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((2919693933:ℚ)/10000000000),((12026146402894982256510393943237893072222264297621833:ℚ)/36436019848632812500000000000000000000000000000000000),((25051939037475138885099041:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((1834573357:ℚ)/2500000000),((7562630451:ℚ)/10000000000),((-64628934961:ℚ)/106800000000),((-1354573357:ℚ)/2717500000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((526380391:ℚ)/2000000000),((3282097464515106210560876110125120401:ℚ)/9858716343750000000000000000000000000),((398994404705598724776813329:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((3729065907:ℚ)/5000000000),((240073511:ℚ)/312500000),((-2060808621:ℚ)/3396875000),((-2769065907:ℚ)/5530000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1935212277:ℚ)/10000000000),((3412909629146350481917242681314761342074026802881559681:ℚ)/10258100100390625000000000000000000000000000000000000000),((1581120639668130755754280529:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((1894483077:ℚ)/2500000000),((3960849089:ℚ)/5000000000),((-34289339979:ℚ)/55300000000),((-1414483077:ℚ)/2860000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((762240117:ℚ)/10000000000),((588394664175928574728644766607814111:ℚ)/1739738000000000000000000000000000000),((391511233093602821736169409:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((7817427297:ℚ)/10000000000),((4438994289:ℚ)/5000000000),((-39548937179:ℚ)/57200000000),((-1965809099:ℚ)/4320000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((274573589482079166628215858636040601:ℚ)/741312000000000000000000000000000000),((433031459:ℚ)/1024000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((1754845023:ℚ)/2000000000),((674184931:ℚ)/625000000),((-2085344747:ℚ)/2700000000),((-1370845023:ℚ)/3200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((139683023938976859875121142753456063:ℚ)/345600000000000000000000000000000000),((433031459:ℚ)/1024000000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((1335489607:ℚ)/1250000000),((14597458933:ℚ)/10000000000),((-142012048263:ℚ)/160000000000),((-1095489607:ℚ)/2760000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((593269323964311275313653:ℚ)/1269600000000000000000000),((433031459:ℚ)/1024000000)⟩
theorem valid12 : Valid source31 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source31 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source31 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source31 nn0 nn1 Qcell ((2117:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source31 nn0 nn1 Qcell ((2117:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC06
#check @N11Formalization.C450Source31GroupedC06.bound
#print axioms N11Formalization.C450Source31GroupedC06.valid0
#print axioms N11Formalization.C450Source31GroupedC06.valid1
#print axioms N11Formalization.C450Source31GroupedC06.valid2
#print axioms N11Formalization.C450Source31GroupedC06.valid3
#print axioms N11Formalization.C450Source31GroupedC06.valid4
#print axioms N11Formalization.C450Source31GroupedC06.valid5
#print axioms N11Formalization.C450Source31GroupedC06.valid6
#print axioms N11Formalization.C450Source31GroupedC06.valid7
#print axioms N11Formalization.C450Source31GroupedC06.valid8
#print axioms N11Formalization.C450Source31GroupedC06.valid9
#print axioms N11Formalization.C450Source31GroupedC06.valid10
#print axioms N11Formalization.C450Source31GroupedC06.valid11
#print axioms N11Formalization.C450Source31GroupedC06.valid12
#print axioms N11Formalization.C450Source31GroupedC06.bound
#print axioms N11Formalization.C450Source31GroupedC06.endpoint_checks
