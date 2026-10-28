import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((3124354639:ℚ)/5000000000),((6536568543:ℚ)/10000000000),((-8089705629:ℚ)/99200000000),((-84354639:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1513833561:ℚ)/2500000000),((131938966636382078219258413232156336832957735133860640151:ℚ)/1654030126953125000000000000000000000000000000000000000000),((-35152912586627265714461379:ℚ)/462080000000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((259509691:ℚ)/400000000),((1355124759:ℚ)/2000000000),((-1761374277:ℚ)/20600000000),((-16309691:ℚ)/2136000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((2739211881:ℚ)/5000000000),((61862935269367578357916876272829575238999182036005027:ℚ)/784207515600000000000000000000000000000000000000000000),((-247023234522999194698219:ℚ)/2957312000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((6726665199:ℚ)/10000000000),((3447555131:ℚ)/5000000000),((-1527555131:ℚ)/17800000000),((-646665199:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((484114293:ℚ)/1000000000),((3471092818671991922440566859966602844118128923525627460969:ℚ)/44651769440234375000000000000000000000000000000000000000000),((-504580563678752603847484297:ℚ)/5544960000000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((3423044517:ℚ)/5000000000),((7014571197:ℚ)/10000000000),((-9523713591:ℚ)/108700000000),((-383044517:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((449185257:ℚ)/1000000000),((260565922034389001492126758410481312987329657171348661343:ℚ)/3365939095440673828125000000000000000000000000000000000000),((-131329137438651152520556033:ℚ)/1386240000000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((3482744763:ℚ)/5000000000),((7134007909:ℚ)/10000000000),((-9882023727:ℚ)/110600000000),((-442744763:ℚ)/28125000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1028813111:ℚ)/2500000000),((34743928158598721995597735524948667872505539717025201127:ℚ)/450540706515312194824218750000000000000000000000000000000),((-136518202349063350652995393:ℚ)/1386240000000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((7084867871:ℚ)/10000000000),((362671081:ℚ)/500000000),((-170671081:ℚ)/1875000000),((-1004867871:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1851491191:ℚ)/5000000000),((134827660178239897445483047102202394369224064028521100507:ℚ)/1754524200000000000000000000000000000000000000000000000000),((-188949845537402203695273059:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((225132037:ℚ)/312500000),((1843203367:ℚ)/2500000000),((-2649610101:ℚ)/28600000000),((-35132037:ℚ)/1817187500),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1620709659:ℚ)/5000000000),((15800456604845256742058206531957560335722005231824253:ℚ)/206272783482074737548828125000000000000000000000000000),((-191291312586564760586931:ℚ)/1805000000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((3661781253:ℚ)/5000000000),((187304613:ℚ)/250000000),((-273913839:ℚ)/2907500000),((-621781253:ℚ)/29550000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1352701411:ℚ)/5000000000),((66319332891779343238309393279596098161271778223655195587:ℚ)/868317265527343750000000000000000000000000000000000000000),((-152116276303694996365927873:ℚ)/1386240000000000000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((744288081:ℚ)/1000000000),((7730868157:ℚ)/10000000000),((-3890868157:ℚ)/39400000000),((-136288081:ℚ)/6100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((254614941:ℚ)/1250000000),((32092303842335400435064754552136454168078039977259776209:ℚ)/419205534375000000000000000000000000000000000000000000000),((-6293042732828420464801417:ℚ)/55449600000000000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((3840731977:ℚ)/5000000000),((8208025791:ℚ)/10000000000),((-13104077373:ℚ)/122000000000),((-266910659:ℚ)/10800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((6158303091295395987273373080580017791231668965078093227:ℚ)/80044200000000000000000000000000000000000000000000000000),((-473787:ℚ)/4000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((2039609627:ℚ)/2500000000),((316081137:ℚ)/312500000),((-21786793:ℚ)/150000000),((-519609627:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((6032462182017481010749265585869187683540109017813687631:ℚ)/75000000000000000000000000000000000000000000000000000000),((-473787:ℚ)/4000000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((10064452363:ℚ)/10000000000),((6961146703:ℚ)/5000000000),((-15123440109:ℚ)/80000000000),((-3984452363:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((281325145825452730137191741077762004640548808060641495399:ℚ)/3153686400000000000000000000000000000000000000000000000000),((-473787:ℚ)/4000000)⟩
theorem valid11 : Valid source20 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source20 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC14
#check @N11Formalization.C450Source20GroupedC14.bound
#print axioms N11Formalization.C450Source20GroupedC14.valid0
#print axioms N11Formalization.C450Source20GroupedC14.valid1
#print axioms N11Formalization.C450Source20GroupedC14.valid2
#print axioms N11Formalization.C450Source20GroupedC14.valid3
#print axioms N11Formalization.C450Source20GroupedC14.valid4
#print axioms N11Formalization.C450Source20GroupedC14.valid5
#print axioms N11Formalization.C450Source20GroupedC14.valid6
#print axioms N11Formalization.C450Source20GroupedC14.valid7
#print axioms N11Formalization.C450Source20GroupedC14.valid8
#print axioms N11Formalization.C450Source20GroupedC14.valid9
#print axioms N11Formalization.C450Source20GroupedC14.valid10
#print axioms N11Formalization.C450Source20GroupedC14.valid11
#print axioms N11Formalization.C450Source20GroupedC14.bound
#print axioms N11Formalization.C450Source20GroupedC14.endpoint_checks
