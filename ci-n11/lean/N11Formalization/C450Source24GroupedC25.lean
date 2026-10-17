import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((2817831147:ℚ)/5000000000),((247654067:ℚ)/400000000),((3697831147:ℚ)/6675000000),((2817686603:ℚ)/3968000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((91930207:ℚ)/125000000),((-2286857130101834294921499087320021:ℚ)/37176099609375000000000000000000000),((-351490135251163252273:ℚ)/924160000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((3057009009:ℚ)/5000000000),((643036071:ℚ)/1000000000),((3937009009:ℚ)/6912500000),((7259324639:ℚ)/10680000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6360034709:ℚ)/10000000000),((-34363757283354059623765507147142627993408802479514241:ℚ)/442362872314453125000000000000000000000000000000000000),((-417344154848920133771:ℚ)/1083000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/2),((9:ℚ)/16),((3176510633:ℚ)/5000000000),((130996533:ℚ)/200000000),((1352170211:ℚ)/2343750000),((1473368797:ℚ)/2212000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((580982431:ℚ)/1000000000),((-126577825988183342523805661883980467653692140496357:ℚ)/1490116119384765625000000000000000000000000000000000),((-33600415413803547193:ℚ)/86640000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((3236242231:ℚ)/5000000000),((6669268601:ℚ)/10000000000),((4116242231:ℚ)/7150000000),((74743417409:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5516847939:ℚ)/10000000000),((-8814924069334462470863628852963271838111430266348569:ℚ)/103842578125000000000000000000000000000000000000000000),((-224141707977269305298857:ℚ)/577600000000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((6591923761:ℚ)/10000000000),((6788687751:ℚ)/10000000000),((8351923761:ℚ)/14537500000),((5832168443:ℚ)/8800000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1302316543:ℚ)/2500000000),((-203538008313461282069475164887347584855541377462140221:ℚ)/2400265116882324218750000000000000000000000000000000000),((-672781096632212852527121:ℚ)/1732800000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((1677835087:ℚ)/2500000000),((1727021303:ℚ)/2500000000),((705945029:ℚ)/1231250000),((19223191727:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4884290521:ℚ)/10000000000),((-370444875212015522011609428053287764754035966247643:ℚ)/4374717521667480468750000000000000000000000000000000),((-28044844413702237584551:ℚ)/72200000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((683073533:ℚ)/1000000000),((281098481:ℚ)/400000000),((859073533:ℚ)/1501250000),((3118686329:ℚ)/4728000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1134538617:ℚ)/2500000000),((-2681273789459018248133376473155462258980326724169291:ℚ)/31719792498779296875000000000000000000000000000000000),((-359099023340438472977:ℚ)/924160000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((6950109743:ℚ)/10000000000),((1429363833:ℚ)/2000000000),((8710109743:ℚ)/15250000000),((15808274497:ℚ)/24020000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2082776607:ℚ)/5000000000),((-934895335635732591049270529038842786563806754223052827:ℚ)/11083056640625000000000000000000000000000000000000000000),((-26939373588715612367069:ℚ)/69312000000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((7069464559:ℚ)/10000000000),((7385478023:ℚ)/10000000000),((8829464559:ℚ)/15725000000),((81189302207:ℚ)/122000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((751717703:ℚ)/2000000000),((-237221621168741889158300101479740090207568596747051699:ℚ)/3037819689941406250000000000000000000000000000000000000),((-223291769327414962463503:ℚ)/577600000000000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((7308118983:ℚ)/10000000000),((1524813691:ℚ)/2000000000),((9068118983:ℚ)/16200000000),((16667323219:ℚ)/25160000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2780423539:ℚ)/10000000000),((-38305510235861247873628579613517488445266372232341449:ℚ)/492075000000000000000000000000000000000000000000000000),((-376465531946470383:ℚ)/972800000000000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((1886676311:ℚ)/2500000000),((4765458857:ℚ)/5000000000),((2326676311:ℚ)/5000000000),((50249129713:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((18515037:ℚ)/156250000),((-849395264530895112220160055772111:ℚ)/46875000000000000000000000000000000),((-95175455529530111:ℚ)/243200000000000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((4726764171:ℚ)/5000000000),((2667788091:ℚ)/2000000000),((5606764171:ℚ)/13800000000),((26954092819:ℚ)/32000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1558030655555032697913713:ℚ)/47610000000000000000000000),((-50216857:ℚ)/128000000)⟩
theorem valid11 : Valid source24 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source24 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source24 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC25
#check @N11Formalization.C450Source24GroupedC25.bound
#print axioms N11Formalization.C450Source24GroupedC25.valid0
#print axioms N11Formalization.C450Source24GroupedC25.valid1
#print axioms N11Formalization.C450Source24GroupedC25.valid2
#print axioms N11Formalization.C450Source24GroupedC25.valid3
#print axioms N11Formalization.C450Source24GroupedC25.valid4
#print axioms N11Formalization.C450Source24GroupedC25.valid5
#print axioms N11Formalization.C450Source24GroupedC25.valid6
#print axioms N11Formalization.C450Source24GroupedC25.valid7
#print axioms N11Formalization.C450Source24GroupedC25.valid8
#print axioms N11Formalization.C450Source24GroupedC25.valid9
#print axioms N11Formalization.C450Source24GroupedC25.valid10
#print axioms N11Formalization.C450Source24GroupedC25.valid11
#print axioms N11Formalization.C450Source24GroupedC25.bound
#print axioms N11Formalization.C450Source24GroupedC25.endpoint_checks
