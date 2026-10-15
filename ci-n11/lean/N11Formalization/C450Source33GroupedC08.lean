import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((1345258367:ℚ)/2000000000),((6949494489:ℚ)/10000000000),((-42705450401:ℚ)/99200000000),((-277752789:ℚ)/842500000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4842198351:ℚ)/10000000000),((836397178034563227922778300116872446407:ℚ)/3050598400000000000000000000000000000000),((155901481350820927902365671:ℚ)/591462400000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((1711707293:ℚ)/2500000000),((175242803:ℚ)/250000000),((-1081185227:ℚ)/2527500000),((-1071707293:ℚ)/3189062500),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((897921863:ℚ)/2000000000),((171091592157517351720736681393469004341868397060011:ℚ)/630715534057617187500000000000000000000000000000000),((237561370524362825279442911:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((690707233:ℚ)/1000000000),((176747847:ℚ)/250000000),((-1094730623:ℚ)/2551250000),((-434707233:ℚ)/1287500000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((17213471:ℚ)/40000000),((25995273700616224576260556152977601688198561176761:ℚ)/95802526904296875000000000000000000000000000000000),((37522652546292100078460071:ℚ)/147865600000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((870912391:ℚ)/1250000000),((7130100217:ℚ)/10000000000),((-44330901953:ℚ)/103000000000),((-550912391:ℚ)/1624218750),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((821859171:ℚ)/2000000000),((724109223541473093410752041789640619841563252521343961:ℚ)/2667790527343750000000000000000000000000000000000000000),((57863369550550244695957559:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((3513755013:ℚ)/5000000000),((7190271563:ℚ)/10000000000),((-4079313097:ℚ)/9450000000),((-2233755013:ℚ)/6556250000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3906220841:ℚ)/10000000000),((974221427824467201497453250509429912527194984632923:ℚ)/3588046875000000000000000000000000000000000000000000),((913488247459360761207317391:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7087705469:ℚ)/10000000000),((725042833:ℚ)/1000000000),((-4541385497:ℚ)/10490000000),((-4527705469:ℚ)/13231250000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((92316289:ℚ)/250000000),((195959006142920447615130014306461056352951424293474249:ℚ)/721450405625000000000000000000000000000000000000000000),((3604357145047265128085563679:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((7147885883:ℚ)/10000000000),((7310570919:ℚ)/10000000000),((-45955138271:ℚ)/105850000000),((-4587885883:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((3466642661:ℚ)/10000000000),((151057894721372031205643304133993525119686934140557262021:ℚ)/555922008574218750000000000000000000000000000000000000000),((3554467998170933216568102671:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((3604025841:ℚ)/5000000000),((7370699713:ℚ)/10000000000),((-46496297417:ℚ)/106800000000),((-2324025841:ℚ)/6734375000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((806393417:ℚ)/2500000000),((620907241341732893577260726342170990798949512218340755923:ℚ)/2284099560000000000000000000000000000000000000000000000000),((876071357960349852399633159:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((3634101631:ℚ)/5000000000),((1857703771:ℚ)/2500000000),((-11759333939:ℚ)/26937500000),((-2354101631:ℚ)/6793750000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1482883659:ℚ)/5000000000),((3322436761521144122675739969491318986593442109235737947:ℚ)/12216642913818359375000000000000000000000000000000000000),((863452333844586654195861479:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((1832085251:ℚ)/2500000000),((3775503487:ℚ)/5000000000),((-24059531383:ℚ)/54350000000),((-170297893:ℚ)/493750000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2681775693:ℚ)/10000000000),((5169617262302750907634936385316500653586988876576241573:ℚ)/18813947797851562500000000000000000000000000000000000000),((212689975169356800240990239:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((7448576441:ℚ)/10000000000),((7791244589:ℚ)/10000000000),((-50281201301:ℚ)/110600000000),((-4888576441:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1999533361:ℚ)/10000000000),((33845712972767064316188337816978635613099115141070017419:ℚ)/120794555000000000000000000000000000000000000000000000000),((9142988405527396151289119:ℚ)/40960000000000000000000000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((3844448329:ℚ)/5000000000),((546910413:ℚ)/625000000),((-3682193717:ℚ)/7150000000),((-2564448329:ℚ)/8100000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((59236895459705015210198546251028941:ℚ)/191709375000000000000000000000000000),((219521821:ℚ)/1024000000)⟩
theorem valid11 : Valid source33 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((1729699847:ℚ)/2000000000),((5331921159:ℚ)/5000000000),((-38067290431:ℚ)/64800000000),((-1217699847:ℚ)/4000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((198398881937900324731117073600556053:ℚ)/583200000000000000000000000000000000),((219521821:ℚ)/1024000000)⟩
theorem valid12 : Valid source33 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((5281086399:ℚ)/5000000000),((14479360453:ℚ)/10000000000),((-110474244077:ℚ)/160000000000),((-4001086399:ℚ)/13800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((6475543238601194369286612151534031927:ℚ)/16000000000000000000000000000000000000),((219521821:ℚ)/1024000000)⟩
theorem valid13 : Valid source33 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source33 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source33 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source33 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC08
#check @N11Formalization.C450Source33GroupedC08.bound
#print axioms N11Formalization.C450Source33GroupedC08.valid0
#print axioms N11Formalization.C450Source33GroupedC08.valid1
#print axioms N11Formalization.C450Source33GroupedC08.valid2
#print axioms N11Formalization.C450Source33GroupedC08.valid3
#print axioms N11Formalization.C450Source33GroupedC08.valid4
#print axioms N11Formalization.C450Source33GroupedC08.valid5
#print axioms N11Formalization.C450Source33GroupedC08.valid6
#print axioms N11Formalization.C450Source33GroupedC08.valid7
#print axioms N11Formalization.C450Source33GroupedC08.valid8
#print axioms N11Formalization.C450Source33GroupedC08.valid9
#print axioms N11Formalization.C450Source33GroupedC08.valid10
#print axioms N11Formalization.C450Source33GroupedC08.valid11
#print axioms N11Formalization.C450Source33GroupedC08.valid12
#print axioms N11Formalization.C450Source33GroupedC08.valid13
#print axioms N11Formalization.C450Source33GroupedC08.bound
#print axioms N11Formalization.C450Source33GroupedC08.endpoint_checks
