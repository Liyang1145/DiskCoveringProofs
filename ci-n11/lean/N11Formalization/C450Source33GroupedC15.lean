import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/8),((-1:ℚ)/16),((6146959697:ℚ)/10000000000),((3236923653:ℚ)/5000000000),((1723076347:ℚ)/25750000000),((14333040303:ℚ)/99200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6286697783:ℚ)/10000000000),((-1710596891497272936786064017623356887511948219330102913377:ℚ)/30764960361328125000000000000000000000000000000000000000000),((-2394549096954357290676547041:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((6389469567:ℚ)/10000000000),((164869641:ℚ)/250000000),((83130359:ℚ)/1311250000),((14090530433:ℚ)/103000000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5721853521:ℚ)/10000000000),((-197698315920882306645780682615526020196390241759213137:ℚ)/3737239918591613769531250000000000000000000000000000000),((-2565144028642561932973463361:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((1627646067:ℚ)/2500000000),((3357822013:ℚ)/5000000000),((534059329:ℚ)/8900000000),((3492353933:ℚ)/26225000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((542044333:ℚ)/1000000000),((-6097863674078968745101071314979348190549727674387175200977:ℚ)/121210717588906250000000000000000000000000000000000000000000),((-165668634226334505949712361:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/8),((-1:ℚ)/16),((3315806197:ℚ)/5000000000),((3388022303:ℚ)/5000000000),((1571977697:ℚ)/26937500000),((2308064601:ℚ)/17800000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2551678493:ℚ)/5000000000),((-55641637609684844669738803537376970950540446440482112257:ℚ)/1134000334222912788391113281250000000000000000000000000000),((-684106885555505821138426041:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((3346047739:ℚ)/5000000000),((6836426801:ℚ)/10000000000),((3083573199:ℚ)/54350000000),((6893952261:ℚ)/53875000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4937983871:ℚ)/10000000000),((-891828169398656925992936119677111163365065864321325498090327:ℚ)/18639454703342421875000000000000000000000000000000000000000000),((-694839716327394282670973529:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((6752558657:ℚ)/10000000000),((1379358221:ℚ)/2000000000),((604641779:ℚ)/10965000000),((13727441343:ℚ)/108700000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2383711407:ℚ)/5000000000),((-3785069447640702227839037316234446134810880608394566117601:ℚ)/81130428079273652343750000000000000000000000000000000000000),((-2822335056754295981759211201:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((1703250617:ℚ)/2500000000),((3478568997:ℚ)/5000000000),((1481431003:ℚ)/27650000000),((1138916461:ℚ)/9137500000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4591090147:ℚ)/10000000000),((-2150564437459763607344093225906929999076771377057629999271:ℚ)/47276293362564697265625000000000000000000000000000000000000),((-179084777548425288279730161:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((1718356857:ℚ)/2500000000),((1769445337:ℚ)/2500000000),((710554663:ℚ)/14062500000),((3401643143:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1102071931:ℚ)/2500000000),((-3408499685361611779858332141959831842162755559696831963:ℚ)/78844623640179634094238281250000000000000000000000000000),((-181776458089919182426156401:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((6994222771:ℚ)/10000000000),((7198360351:ℚ)/10000000000),((2721639649:ℚ)/57200000000),((13485777229:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((80393787:ℚ)/200000000),((-129728032482410855267845712389660243282784304450809919739:ℚ)/3158143560000000000000000000000000000000000000000000000000),((-2994694813338759392385615209:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((7114948469:ℚ)/10000000000),((3719669041:ℚ)/5000000000),((413443653:ℚ)/9850000000),((1028080887:ℚ)/8800000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3592025987:ℚ)/10000000000),((-669001771360596190780850092075074289780360529148281661:ℚ)/18068166660156250000000000000000000000000000000000000000),((-3081151791962767309446517689:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((1471240959:ℚ)/2000000000),((3840047343:ℚ)/5000000000),((1119952657:ℚ)/30500000000),((2624759041:ℚ)/23640000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((634934071:ℚ)/2500000000),((-68767864907820756620431492154881666338977171425373559645043:ℚ)/2064587256796875000000000000000000000000000000000000000000000),((-130185224098126304173179969:ℚ)/591462400000000000000000000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((7597221891:ℚ)/10000000000),((8161024297:ℚ)/10000000000),((1758975703:ℚ)/64800000000),((12882778109:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((135196697:ℚ)/5000000000),((-5623101106963541790687579275465473293395852587048583256637:ℚ)/210932475840000000000000000000000000000000000000000000000000),((-3428875143567536970472733769:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid source33 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((8078624879:ℚ)/10000000000),((1259881577:ℚ)/1250000000),((-19881577:ℚ)/8100000000),((1377930569:ℚ)/14400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-426518941839068570133216899903363781205955141881733:ℚ)/62278242187500000000000000000000000000000000000000000),((-47519239:ℚ)/204800000)⟩
theorem valid12 : Valid source33 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((399922573:ℚ)/400000000),((556057639:ℚ)/400000000),((-159257639:ℚ)/3200000000),((419277427:ℚ)/6400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2727352023652729131797119421472133:ℚ)/102400000000000000000000000000000000),((-47519239:ℚ)/204800000)⟩
theorem valid13 : Valid source33 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC15
#check @N11Formalization.C450Source33GroupedC15.bound
#print axioms N11Formalization.C450Source33GroupedC15.valid0
#print axioms N11Formalization.C450Source33GroupedC15.valid1
#print axioms N11Formalization.C450Source33GroupedC15.valid2
#print axioms N11Formalization.C450Source33GroupedC15.valid3
#print axioms N11Formalization.C450Source33GroupedC15.valid4
#print axioms N11Formalization.C450Source33GroupedC15.valid5
#print axioms N11Formalization.C450Source33GroupedC15.valid6
#print axioms N11Formalization.C450Source33GroupedC15.valid7
#print axioms N11Formalization.C450Source33GroupedC15.valid8
#print axioms N11Formalization.C450Source33GroupedC15.valid9
#print axioms N11Formalization.C450Source33GroupedC15.valid10
#print axioms N11Formalization.C450Source33GroupedC15.valid11
#print axioms N11Formalization.C450Source33GroupedC15.valid12
#print axioms N11Formalization.C450Source33GroupedC15.valid13
#print axioms N11Formalization.C450Source33GroupedC15.bound
#print axioms N11Formalization.C450Source33GroupedC15.endpoint_checks
