import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((197779829:ℚ)/312500000),((413594421:ℚ)/625000000),((-285594421:ℚ)/1240000000),((-112779829:ℚ)/804687500),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1466817591:ℚ)/2500000000),((10719602372038771804584673910933876972722351775186591:ℚ)/151430980861186981201171875000000000000000000000000000),((672672544652228597023:ℚ)/22562500000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((3283802671:ℚ)/5000000000),((3428086137:ℚ)/5000000000),((-2404086137:ℚ)/10300000000),((-641267557:ℚ)/4450000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5273204019:ℚ)/10000000000),((497947052442848144840953859659562709735929581129312217:ℚ)/7090996777343750000000000000000000000000000000000000000),((70925669823707548800699:ℚ)/2888000000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((6806173709:ℚ)/10000000000),((55803779:ℚ)/80000000),((-39419779:ℚ)/170880000),((-4086173709:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4611324543:ℚ)/10000000000),((1152396260109959171529066499478710602154688974662817404389:ℚ)/16744413540087890625000000000000000000000000000000000000000),((222828883935876127742859:ℚ)/11552000000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((69254297:ℚ)/100000000),((7094753449:ℚ)/10000000000),((-5046753449:ℚ)/21740000000),((-42054297:ℚ)/276500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1061274459:ℚ)/2500000000),((974663967859468304164037638913560626724419301603:ℚ)/14202274664306640625000000000000000000000000000000),((53276537557968591:ℚ)/3200000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((7044668199:ℚ)/10000000000),((7154387157:ℚ)/10000000000),((-5106387157:ℚ)/22120000000),((-4324668199:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((76929891:ℚ)/200000000),((22757085210981252395384427244731125336507045718344214747:ℚ)/334646186404800415039062500000000000000000000000000000000),((161784955877097136868739:ℚ)/11552000000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((7104281171:ℚ)/10000000000),((1803504117:ℚ)/2500000000),((-1291504117:ℚ)/5577500000),((-1461427057:ℚ)/9375000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((726348871:ℚ)/2000000000),((4572646030539840704504835565926561758346324746635009687:ℚ)/67320093512535095214843750000000000000000000000000000000),((146497182164059570758699:ℚ)/11552000000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((71638901:ℚ)/100000000),((1818410373:ℚ)/2500000000),((-1306410373:ℚ)/5625000000),((-44438901:ℚ)/283625000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((3324338:ℚ)/9765625),((108843298743168268607692889430426812049868861063:ℚ)/1604227904983520507812500000000000000000000000000),((13119864106839525039:ℚ)/1155200000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((451468443:ℚ)/625000000),((7333262339:ℚ)/10000000000),((-5285262339:ℚ)/22690000000),((-281468443:ℚ)/1787500000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3160843197:ℚ)/10000000000),((2744675768532556536160862575518129651328703663941994109:ℚ)/40496982928466796875000000000000000000000000000000000000),((626998078165351713:ℚ)/62500000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((3641548117:ℚ)/5000000000),((7452491909:ℚ)/10000000000),((-5404491909:ℚ)/22880000000),((-2281548117:ℚ)/14537500000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((724490471:ℚ)/2500000000),((93536658648054585447924948310749200170543035091768770753:ℚ)/1372951646856689453125000000000000000000000000000000000000),((25142290548272154035571:ℚ)/2888000000000000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((3701143691:ℚ)/5000000000),((1892926493:ℚ)/2500000000),((-1380926493:ℚ)/5815000000),((-2341143691:ℚ)/14775000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((457194947:ℚ)/2000000000),((7379359090805000112301814131784069156432173364397109737:ℚ)/108539658190917968750000000000000000000000000000000000000),((17474084211049290993059:ℚ)/2888000000000000000000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((7521464271:ℚ)/10000000000),((1952522623:ℚ)/2500000000),((-1440522623:ℚ)/5910000000),((-4801464271:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((11510827:ℚ)/80000000),((1199156802255948914554755873815433094955929816276346164481:ℚ)/17466897265625000000000000000000000000000000000000000000000),((39179995303974787196499:ℚ)/11552000000000000000000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((1551955591:ℚ)/2000000000),((8286703137:ℚ)/10000000000),((-6238703137:ℚ)/24400000000),((-335985197:ℚ)/2160000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((44739067773240288420857723846573286230251028136657313:ℚ)/640353600000000000000000000000000000000000000000000000),((104779:ℚ)/64000000)⟩
theorem valid11 : Valid source18 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((8236261509:ℚ)/10000000000),((1273952001:ℚ)/1250000000),((-1017952001:ℚ)/3240000000),((-5516261509:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1242681226063335158230127005952860063886687582062042527247:ℚ)/16200000000000000000000000000000000000000000000000000000000),((104779:ℚ)/64000000)⟩
theorem valid12 : Valid source18 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((1014078153:ℚ)/1000000000),((6998687093:ℚ)/5000000000),((-5974687093:ℚ)/16000000000),((-742078153:ℚ)/5520000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((34112439056786529327901282468428318329980201815506033:ℚ)/394210800000000000000000000000000000000000000000000000),((104779:ℚ)/64000000)⟩
theorem valid13 : Valid source18 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source18 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source18 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2269:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source18 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source18 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC12
#check @N11Formalization.C450Source18GroupedC12.bound
#print axioms N11Formalization.C450Source18GroupedC12.valid0
#print axioms N11Formalization.C450Source18GroupedC12.valid1
#print axioms N11Formalization.C450Source18GroupedC12.valid2
#print axioms N11Formalization.C450Source18GroupedC12.valid3
#print axioms N11Formalization.C450Source18GroupedC12.valid4
#print axioms N11Formalization.C450Source18GroupedC12.valid5
#print axioms N11Formalization.C450Source18GroupedC12.valid6
#print axioms N11Formalization.C450Source18GroupedC12.valid7
#print axioms N11Formalization.C450Source18GroupedC12.valid8
#print axioms N11Formalization.C450Source18GroupedC12.valid9
#print axioms N11Formalization.C450Source18GroupedC12.valid10
#print axioms N11Formalization.C450Source18GroupedC12.valid11
#print axioms N11Formalization.C450Source18GroupedC12.valid12
#print axioms N11Formalization.C450Source18GroupedC12.valid13
#print axioms N11Formalization.C450Source18GroupedC12.bound
#print axioms N11Formalization.C450Source18GroupedC12.endpoint_checks
