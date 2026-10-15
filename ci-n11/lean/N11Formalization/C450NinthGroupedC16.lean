import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC16
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((-1:ℚ)/16),(0:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/16),(0:ℚ),((3095868213:ℚ)/5000000000),((267494207:ℚ)/400000000),((-88294207:ℚ)/3968000000),((8:ℚ)/155),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6185809391:ℚ)/10000000000),((4710534693626621:ℚ)/238328000000000000),((-470152745330862091997203:ℚ)/23658496000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((6667325173:ℚ)/10000000000),((6806238951:ℚ)/10000000000),((-2326238951:ℚ)/106800000000),((64:ℚ)/1335),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5006315037:ℚ)/10000000000),((53432771899666064800062221463889:ℚ)/2788207470703125000000000000000000),((-999434810786165934924617641:ℚ)/44359680000000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((3393104737:ℚ)/5000000000),((3462559061:ℚ)/5000000000),((-1222559061:ℚ)/54350000000),((256:ℚ)/5435),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4670014079:ℚ)/10000000000),((112084007647945814102359569754427:ℚ)/5879358686828613281250000000000000),((-85674586782270046049158587:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/16),(0:ℚ),((6905089153:ℚ)/10000000000),((873069507:ℚ)/1250000000),((-313069507:ℚ)/13825000000),((128:ℚ)/2765),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((4309618499:ℚ)/10000000000),((11180354108370570763625711759809:ℚ)/589817163085937500000000000000000),((-16520075293680521962463809:ℚ)/693120000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/16),(0:ℚ),((3482263667:ℚ)/5000000000),((1760998231:ℚ)/2500000000),((-640998231:ℚ)/27887500000),((512:ℚ)/11155),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4118416341:ℚ)/10000000000),((27866024816425074665921447534087:ℚ)/1473400930786132812500000000000000),((-22325048529100538922425667:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/16),(0:ℚ),((1404792889:ℚ)/2000000000),((1420685751:ℚ)/2000000000),((-524685751:ℚ)/22500000000),((256:ℚ)/5625),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((979613747:ℚ)/2500000000),((328002876707801505685588181154317:ℚ)/17380714416503906250000000000000000),((-43436597104903512151935241:ℚ)/1774387200000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/16),(0:ℚ),((1416680103:ℚ)/2000000000),((3581431787:ℚ)/5000000000),((-1341431787:ℚ)/56725000000),((512:ℚ)/11345),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((927078451:ℚ)/2500000000),((6713648771748232547838664816201:ℚ)/356495089996337890625000000000000),((-91685218394505048095683643:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/16),(0:ℚ),((7142835569:ℚ)/10000000000),((3611148703:ℚ)/5000000000),((-1371148703:ℚ)/57200000000),((32:ℚ)/715),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((43576853:ℚ)/125000000),((4025387512091564527858728833881:ℚ)/214175317382812500000000000000000),((-92877117915345256787527123:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((112535463:ℚ)/156250000),((1820432569:ℚ)/2500000000),((-233477523:ℚ)/9612500000),((512:ℚ)/11535),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3249488533:ℚ)/10000000000),((9372174431273922676814304378287:ℚ)/499610532348632812500000000000000),((-23517152429539578732994467:ℚ)/924160000000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-1:ℚ)/16),(0:ℚ),((7261702729:ℚ)/10000000000),((3670581103:ℚ)/5000000000),((-1430581103:ℚ)/58150000000),((256:ℚ)/5815),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2994895901:ℚ)/10000000000),((134832993721647236532445318995173:ℚ)/7200795350646972656250000000000000),((-95259694325131446934183923:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((7321134883:ℚ)/10000000000),((7400593221:ℚ)/10000000000),((-417227603:ℚ)/16750000000),((512:ℚ)/11725),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((42458271:ℚ)/156250000),((735591730825608959682568466022931:ℚ)/39353068923950195312500000000000000),((-1157404466565033246348097681:ℚ)/44359680000000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((7380566117:ℚ)/10000000000),((7519452587:ℚ)/10000000000),((-3039452587:ℚ)/118200000000),((128:ℚ)/2955),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((301106811:ℚ)/1250000000),((282370391482740628521474257116261:ℚ)/15119023754882812500000000000000000),((-390367095542548607958746043:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-1:ℚ)/16),(0:ℚ),((7499425913:ℚ)/10000000000),((3819154271:ℚ)/5000000000),((-1579154271:ℚ)/60050000000),((256:ℚ)/6005),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((50895733:ℚ)/312500000),((393718352839945530823627129950713:ℚ)/21146528332519531250000000000000000),((-138507441095651:ℚ)/5120000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/16),(0:ℚ),((1904570571:ℚ)/2500000000),((8113701257:ℚ)/10000000000),((-3633701257:ℚ)/122000000000),((64:ℚ)/1525),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((6461531523371836554483638058103:ℚ)/346345520019531250000000000000000),((-5656437:ℚ)/204800000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/16),(0:ℚ),((4046838271:ℚ)/5000000000),((10014898701:ℚ)/10000000000),((-5534898701:ℚ)/129600000000),((16:ℚ)/405),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((366518057054734199697530169301:ℚ)/19461950683593750000000000000000),((-5656437:ℚ)/204800000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/16),(0:ℚ),((4997439343:ℚ)/5000000000),((2763260771:ℚ)/2000000000),((-1867260771:ℚ)/32000000000),((4:ℚ)/125),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((41025626286249:ℚ)/2000000000000000),((-5656437:ℚ)/204800000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC16
#check @N11Formalization.C450NinthGroupedC16.bound
#print axioms N11Formalization.C450NinthGroupedC16.valid0
#print axioms N11Formalization.C450NinthGroupedC16.valid1
#print axioms N11Formalization.C450NinthGroupedC16.valid2
#print axioms N11Formalization.C450NinthGroupedC16.valid3
#print axioms N11Formalization.C450NinthGroupedC16.valid4
#print axioms N11Formalization.C450NinthGroupedC16.valid5
#print axioms N11Formalization.C450NinthGroupedC16.valid6
#print axioms N11Formalization.C450NinthGroupedC16.valid7
#print axioms N11Formalization.C450NinthGroupedC16.valid8
#print axioms N11Formalization.C450NinthGroupedC16.valid9
#print axioms N11Formalization.C450NinthGroupedC16.valid10
#print axioms N11Formalization.C450NinthGroupedC16.valid11
#print axioms N11Formalization.C450NinthGroupedC16.valid12
#print axioms N11Formalization.C450NinthGroupedC16.valid13
#print axioms N11Formalization.C450NinthGroupedC16.valid14
#print axioms N11Formalization.C450NinthGroupedC16.valid15
#print axioms N11Formalization.C450NinthGroupedC16.bound
#print axioms N11Formalization.C450NinthGroupedC16.endpoint_checks
