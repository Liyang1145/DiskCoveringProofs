import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((388245533:ℚ)/625000000),((419731839:ℚ)/625000000),((-219731839:ℚ)/3100000000),((51754467:ℚ)/6200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1534960861:ℚ)/2500000000),((118781751029240330000350261105913:ℚ)/3723875000000000000000000000000000),((-91467322553220971206573:ℚ)/4332000000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((6688039109:ℚ)/10000000000),((1366941947:ℚ)/2000000000),((-726941947:ℚ)/10680000000),((117320297:ℚ)/35600000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1237308231:ℚ)/2500000000),((1634006399208574355911123546764400752102238188502639747:ℚ)/52872675000000000000000000000000000000000000000000000000),((-20114189319162583563981:ℚ)/778240000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((1701752581:ℚ)/2500000000),((347685071:ℚ)/500000000),((-187685071:ℚ)/2717500000),((58247419:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((460884999:ℚ)/1000000000),((15079173637337650973699100459624518207038301985482083:ℚ)/489946557235717773437500000000000000000000000000000000),((-24967510373056376249711:ℚ)/924160000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((346298117:ℚ)/500000000),((3506597083:ℚ)/5000000000),((-1906597083:ℚ)/27650000000),((5701883:ℚ)/5530000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((2121697961:ℚ)/5000000000),((288840877510144498352899970885268892570314934407477:ℚ)/9437074609375000000000000000000000000000000000000000),((-2605625334170087140323319:ℚ)/92416000000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((6985435761:ℚ)/10000000000),((7072684917:ℚ)/10000000000),((-3872684917:ℚ)/55775000000),((54564239:ℚ)/111550000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4049139877:ℚ)/10000000000),((720272773386406209736976231947643047415457702195164929:ℚ)/23574414892578125000000000000000000000000000000000000000),((-31916332525882296943213957:ℚ)/1108992000000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((1761226879:ℚ)/2500000000),((1783043431:ℚ)/2500000000),((-983043431:ℚ)/14062500000),((-1226879:ℚ)/28362500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((3845655279:ℚ)/10000000000),((6116474818917402331580406993545977766340719292834217:ℚ)/200528488122940063476562500000000000000000000000000000),((-678438945590045953652831:ℚ)/23104000000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((3552188823:ℚ)/5000000000),((1797915159:ℚ)/2500000000),((-997915159:ℚ)/14181250000),((-32188823:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3631387003:ℚ)/10000000000),((5051402134090393605419807729866690765726998591736244091749:ℚ)/165875642075000000000000000000000000000000000000000000000000),((-2075857190658730265016253:ℚ)/69312000000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((7163846193:ℚ)/10000000000),((7251145699:ℚ)/10000000000),((-4051145699:ℚ)/57200000000),((-123846193:ℚ)/115350000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3404295143:ℚ)/10000000000),((33943213889880092751307518331599266503365811002255019:ℚ)/1116317283216476440429687500000000000000000000000000000),((-11287423325659672151710471:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((1444662639:ℚ)/2000000000),((45691431:ℚ)/62500000),((-25691431:ℚ)/360468750),((-36662639:ℚ)/23260000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((790403261:ℚ)/2500000000),((344325394565814262189957535922645112976490539089134479491:ℚ)/11340619007278125000000000000000000000000000000000000000000),((-84254723113968248023:ℚ)/2707500000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-1:ℚ)/8),((-1:ℚ)/16),((7282778691:ℚ)/10000000000),((7370110461:ℚ)/10000000000),((-4170110461:ℚ)/58150000000),((-242778691:ℚ)/117250000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2899423677:ℚ)/10000000000),((22202803749295527504263654744380431394896764336206046288471:ℚ)/732281906536865234375000000000000000000000000000000000000000),((-35159109313476931823004373:ℚ)/1108992000000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((7342242717:ℚ)/10000000000),((1485918049:ℚ)/2000000000),((-845918049:ℚ)/11725000000),((-302242717:ℚ)/118200000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((522370707:ℚ)/2000000000),((254471445064345274811202839507596718810651463005655197799:ℚ)/8403937352343750000000000000000000000000000000000000000000),((-477431927371545211264271:ℚ)/14786560000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((7401705309:ℚ)/10000000000),((7548544829:ℚ)/10000000000),((-1449514943:ℚ)/19700000000),((-361705309:ℚ)/120100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((228935201:ℚ)/1000000000),((1009578684859536779764456241616227740011121093956961839959:ℚ)/33326928652050781250000000000000000000000000000000000000000),((-12148766911517038562067911:ℚ)/369664000000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((3760313163:ℚ)/5000000000),((239609157:ℚ)/312500000),((-139609157:ℚ)/1876562500),((-240313163:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1446522347:ℚ)/10000000000),((52758888623598929515327701335914046057522598564825162041:ℚ)/1745672265625000000000000000000000000000000000000000000000),((-4139581586533183:ℚ)/121600000000000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((3819771003:ℚ)/5000000000),((8143227559:ℚ)/10000000000),((-4943227559:ℚ)/61000000000),((-299771003:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((7314072685307273041085489164201243413345898744798116883:ℚ)/240132600000000000000000000000000000000000000000000000000),((-4458741:ℚ)/128000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((8115156053:ℚ)/10000000000),((2511366677:ℚ)/2500000000),((-63383951:ℚ)/600000000),((-1075156053:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((150650434116746789244497414052860152484980700514330269833:ℚ)/4800000000000000000000000000000000000000000000000000000000),((-4458741:ℚ)/128000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((1001702807:ℚ)/1000000000),((13848093383:ℚ)/10000000000),((-10648093383:ℚ)/80000000000),((-99234269:ℚ)/7360000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1342575772258024401467618774192833057120830771340947:ℚ)/38934400000000000000000000000000000000000000000000000),((-4458741:ℚ)/128000000)⟩
theorem valid15 : Valid source12 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC15
#check @N11Formalization.C450Source12GroupedC15.bound
#print axioms N11Formalization.C450Source12GroupedC15.valid0
#print axioms N11Formalization.C450Source12GroupedC15.valid1
#print axioms N11Formalization.C450Source12GroupedC15.valid2
#print axioms N11Formalization.C450Source12GroupedC15.valid3
#print axioms N11Formalization.C450Source12GroupedC15.valid4
#print axioms N11Formalization.C450Source12GroupedC15.valid5
#print axioms N11Formalization.C450Source12GroupedC15.valid6
#print axioms N11Formalization.C450Source12GroupedC15.valid7
#print axioms N11Formalization.C450Source12GroupedC15.valid8
#print axioms N11Formalization.C450Source12GroupedC15.valid9
#print axioms N11Formalization.C450Source12GroupedC15.valid10
#print axioms N11Formalization.C450Source12GroupedC15.valid11
#print axioms N11Formalization.C450Source12GroupedC15.valid12
#print axioms N11Formalization.C450Source12GroupedC15.valid13
#print axioms N11Formalization.C450Source12GroupedC15.valid14
#print axioms N11Formalization.C450Source12GroupedC15.valid15
#print axioms N11Formalization.C450Source12GroupedC15.bound
#print axioms N11Formalization.C450Source12GroupedC15.endpoint_checks
