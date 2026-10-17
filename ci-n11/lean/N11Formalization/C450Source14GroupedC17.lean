import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((24006799:ℚ)/39062500),((6657719207:ℚ)/10000000000),((32:ℚ)/445),((14977719207:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3144712547:ℚ)/5000000000),((75073666750457154675065220570084091783509:ℚ)/1933103194112000000000000000000000000000000),((-1305847288478764582576676451:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((1655573463:ℚ)/2500000000),((6895814403:ℚ)/10000000000),((192:ℚ)/2765),((15215814403:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1282100573:ℚ)/2500000000),((261298739328784503210288756497799017242063074265416492748643681:ℚ)/6984982023440400000000000000000000000000000000000000000000000000),((-1407068700949649580447470891:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((428780631:ℚ)/625000000),((7014846869:ℚ)/10000000000),((128:ℚ)/1875),((15334846869:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4448015659:ℚ)/10000000000),((133540245622883069006676871216697713526236422895440505801:ℚ)/3623836650000000000000000000000000000000000000000000000000),((-1457660600984134749423508539:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),(0:ℚ),((1:ℚ)/16),((3489785253:ℚ)/5000000000),((3537179771:ℚ)/5000000000),((768:ℚ)/11345),((7697179771:ℚ)/56250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1017171433:ℚ)/2500000000),((209630091764276005946202098730828182882335509171314345896856131:ℚ)/5726860304260253906250000000000000000000000000000000000000000000),((-370738089463266334847015259:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((7039106543:ℚ)/10000000000),((44586687:ℚ)/62500000),((48:ℚ)/715),((96586687:ℚ)/709062500),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3865950211:ℚ)/10000000000),((66555682788999126613105479607830855110411442656868627:ℚ)/1822492023833778381347656250000000000000000000000000000),((-58421100382101817438331:ℚ)/577600000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),(0:ℚ),((1:ℚ)/16),((887329987:ℚ)/1250000000),((7193378061:ℚ)/10000000000),((256:ℚ)/3845),((15513378061:ℚ)/114400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((730516403:ℚ)/2000000000),((151224131744309781993600365098903329298030371533152201299655727:ℚ)/4150228741744800000000000000000000000000000000000000000000000000),((-1508207126734319488699123979:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((715817063:ℚ)/1000000000),((7252884019:ℚ)/10000000000),((384:ℚ)/5815),((15572884019:ℚ)/115350000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1713295523:ℚ)/5000000000),((6290071619914952464516312965193727584441843295626931663914033:ℚ)/172993975840834031250000000000000000000000000000000000000000000),((-1520833242535167007562259339:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),(0:ℚ),((1:ℚ)/16),((7217698809:ℚ)/10000000000),((7312387849:ℚ)/10000000000),((768:ℚ)/11725),((15632387849:ℚ)/116300000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3185287021:ℚ)/10000000000),((58853348581875765846478387668495646262311246749339427545254227:ℚ)/1621907605630626562500000000000000000000000000000000000000000000),((-1533458530794609270271072899:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((7277224497:ℚ)/10000000000),((7371889601:ℚ)/10000000000),((64:ℚ)/985),((15691889601:ℚ)/117250000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((365609663:ℚ)/1250000000),((52835475795338872798285467392418661005465712337714149612587:ℚ)/1458868777905273437500000000000000000000000000000000000000000),((-1546083005124821147118260499:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((3668373877:ℚ)/5000000000),((749088707:ℚ)/1000000000),((384:ℚ)/6005),((2675277:ℚ)/20000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((329963501:ℚ)/1250000000),((2611077629114348359048934579523726332326047096494397:ℚ)/72120050000000000000000000000000000000000000000000000),((-15586708973741018443553451:ℚ)/147865600000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((3727893603:ℚ)/5000000000),((951234601:ℚ)/1250000000),((96:ℚ)/1525),((1991234601:ℚ)/15012500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1951188559:ℚ)/10000000000),((2839120385879124691604935552966464219902897521013683378809:ℚ)/78686231925305175781250000000000000000000000000000000000000),((-13025669204193483:ℚ)/121600000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((757481761:ℚ)/1000000000),((1010720659:ℚ)/1250000000),((8:ℚ)/135),((2050720659:ℚ)/15250000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((203571359:ℚ)/2500000000),((48833520942915339140071715990930481024572991543053007473:ℚ)/1346591381835937500000000000000000000000000000000000000000),((-2646770211939321:ℚ)/24320000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((8050856741:ℚ)/10000000000),((9988473359:ℚ)/10000000000),((6:ℚ)/125),((6102824453:ℚ)/43200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3479530364059848756812491763346331049042051096801100271:ℚ)/94478400000000000000000000000000000000000000000000000000),((-111813849:ℚ)/1024000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((995402373:ℚ)/1000000000),((275832993:ℚ)/200000000),((4:ℚ)/115),((442232993:ℚ)/3200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((178270082971604152807444199542114259:ℚ)/4333568000000000000000000000000000000),((-111813849:ℚ)/1024000000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source14 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC17
#check @N11Formalization.C450Source14GroupedC17.bound
#print axioms N11Formalization.C450Source14GroupedC17.valid0
#print axioms N11Formalization.C450Source14GroupedC17.valid1
#print axioms N11Formalization.C450Source14GroupedC17.valid2
#print axioms N11Formalization.C450Source14GroupedC17.valid3
#print axioms N11Formalization.C450Source14GroupedC17.valid4
#print axioms N11Formalization.C450Source14GroupedC17.valid5
#print axioms N11Formalization.C450Source14GroupedC17.valid6
#print axioms N11Formalization.C450Source14GroupedC17.valid7
#print axioms N11Formalization.C450Source14GroupedC17.valid8
#print axioms N11Formalization.C450Source14GroupedC17.valid9
#print axioms N11Formalization.C450Source14GroupedC17.valid10
#print axioms N11Formalization.C450Source14GroupedC17.valid11
#print axioms N11Formalization.C450Source14GroupedC17.valid12
#print axioms N11Formalization.C450Source14GroupedC17.valid13
#print axioms N11Formalization.C450Source14GroupedC17.bound
#print axioms N11Formalization.C450Source14GroupedC17.endpoint_checks
