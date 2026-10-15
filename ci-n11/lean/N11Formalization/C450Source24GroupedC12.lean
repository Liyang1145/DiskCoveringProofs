import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((1590293131:ℚ)/2500000000),((6665404243:ℚ)/10000000000),((-3849404243:ℚ)/19840000000),((-670293131:ℚ)/6437500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((579025349:ℚ)/1000000000),((15954387555308968533067217399442173420228990196899533427:ℚ)/77532662200927734375000000000000000000000000000000000000),((-48899910148798982074153:ℚ)/577600000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((3300431249:ℚ)/5000000000),((6785243481:ℚ)/10000000000),((-3969243481:ℚ)/20600000000),((-1460431249:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5185584827:ℚ)/10000000000),((36628816281011664084060417138281016981386188494913437707:ℚ)/181419413523864746093750000000000000000000000000000000000),((-223813944814351277524473:ℚ)/2310400000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((6720647201:ℚ)/10000000000),((863130431:ℚ)/1250000000),((-511130431:ℚ)/2622500000),((-1013549067:ℚ)/8900000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((194325153:ℚ)/400000000),((116335474845277180831104852197077148858883881918908727463:ℚ)/577744125781250000000000000000000000000000000000000000000),((-951992140513852138345673:ℚ)/9241600000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((6840394623:ℚ)/10000000000),((3512403119:ℚ)/5000000000),((-2104403119:ℚ)/10680000000),((-3160394623:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2254538377:ℚ)/5000000000),((3363495597512255604076966684436175796942967671381926828961:ℚ)/16744413540087890625000000000000000000000000000000000000000),((-3026804266037568902249051:ℚ)/27724800000000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((27187917:ℚ)/39062500),((35722669:ℚ)/50000000),((-21642669:ℚ)/108700000),((-25625834:ℚ)/216015625),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((826584567:ℚ)/2000000000),((91912222241720438800172339967229791356039830609279:ℚ)/458572809415636584162712097167968750000000000000000),((-1081473005452991773:ℚ)/9375000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((1415957087:ℚ)/2000000000),((3602192471:ℚ)/5000000000),((-2194192471:ℚ)/11060000000),((-679957087:ℚ)/5577500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1860708791:ℚ)/5000000000),((3726482303552703488546528305837294357909403392937260219:ℚ)/18740186438668823242187500000000000000000000000000000000),((-44937666408322140800137:ℚ)/369664000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((7139612777:ℚ)/10000000000),((7264227947:ℚ)/10000000000),((-4448227947:ℚ)/22310000000),((-1153204259:ℚ)/9375000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3498540939:ℚ)/10000000000),((13375006445316666461647308554189095594034070185080231843:ℚ)/67320093512535095214843750000000000000000000000000000000),((-1152198391728204154113817:ℚ)/9241600000000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((7199432393:ℚ)/10000000000),((738389037:ℚ)/1000000000),((-456789037:ℚ)/2250000000),((-3519432393:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((163058081:ℚ)/500000000),((131376432676253557752251178582222910966895798886734037637:ℚ)/657946575000000000000000000000000000000000000000000000000),((-1181007281416332377276377:ℚ)/9241600000000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((731904923:ℚ)/1000000000),((7503522647:ℚ)/10000000000),((-4687522647:ℚ)/22880000000),((-363904923:ℚ)/2907500000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3409419:ℚ)/12500000),((168436030217895742150927785301481648634451675082601477:ℚ)/844893321142578125000000000000000000000000000000000000),((-12387818276291359590417:ℚ)/92416000000000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((7438637443:ℚ)/10000000000),((3811563127:ℚ)/5000000000),((-2403563127:ℚ)/11630000000),((-3758637443:ℚ)/29550000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((516084733:ℚ)/2500000000),((172859968292625390202662571133943974949779969664152498127:ℚ)/868317265527343750000000000000000000000000000000000000000),((-1296765857329183836837777:ℚ)/9241600000000000000000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((7558198431:ℚ)/10000000000),((3931126443:ℚ)/5000000000),((-2523126443:ℚ)/11820000000),((-3878198431:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1049309861:ℚ)/10000000000),((10532196346062704040436137795916339566737115028361230169629:ℚ)/52400691796875000000000000000000000000000000000000000000000),((-4064879677283950703080859:ℚ)/27724800000000000000000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((779724389:ℚ)/1000000000),((8340217323:ℚ)/10000000000),((-5524217323:ℚ)/24400000000),((-137241463:ℚ)/1080000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((16377244916956336432841698006572087810436034214662341:ℚ)/80044200000000000000000000000000000000000000000000000),((-19049289:ℚ)/128000000)⟩
theorem valid11 : Valid source24 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((8275060519:ℚ)/10000000000),((5124619811:ℚ)/5000000000),((-3716619811:ℚ)/12960000000),((-4595060519:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3647042365879008912365213249071867707512377305365427464131:ℚ)/16200000000000000000000000000000000000000000000000000000000),((-19049289:ℚ)/128000000)⟩
theorem valid12 : Valid source24 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((10183633873:ℚ)/10000000000),((1757475041:ℚ)/1250000000),((-1405475041:ℚ)/4000000000),((-6503633873:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((100757819212934991598344187528455073577861660692849286759:ℚ)/394210800000000000000000000000000000000000000000000000000),((-19049289:ℚ)/128000000)⟩
theorem valid13 : Valid source24 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC12
#check @N11Formalization.C450Source24GroupedC12.bound
#print axioms N11Formalization.C450Source24GroupedC12.valid0
#print axioms N11Formalization.C450Source24GroupedC12.valid1
#print axioms N11Formalization.C450Source24GroupedC12.valid2
#print axioms N11Formalization.C450Source24GroupedC12.valid3
#print axioms N11Formalization.C450Source24GroupedC12.valid4
#print axioms N11Formalization.C450Source24GroupedC12.valid5
#print axioms N11Formalization.C450Source24GroupedC12.valid6
#print axioms N11Formalization.C450Source24GroupedC12.valid7
#print axioms N11Formalization.C450Source24GroupedC12.valid8
#print axioms N11Formalization.C450Source24GroupedC12.valid9
#print axioms N11Formalization.C450Source24GroupedC12.valid10
#print axioms N11Formalization.C450Source24GroupedC12.valid11
#print axioms N11Formalization.C450Source24GroupedC12.valid12
#print axioms N11Formalization.C450Source24GroupedC12.valid13
#print axioms N11Formalization.C450Source24GroupedC12.bound
#print axioms N11Formalization.C450Source24GroupedC12.endpoint_checks
