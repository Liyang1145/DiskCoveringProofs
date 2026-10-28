import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((754225419:ℚ)/1250000000),((6547749717:ℚ)/10000000000),((5839577933:ℚ)/13350000000),((7187749717:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6535646073:ℚ)/10000000000),((175530101608714013897171:ℚ)/44555625000000000000000000),((-83856388307716629547348889:ℚ)/693120000000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((6509244707:ℚ)/10000000000),((3392706519:ℚ)/5000000000),((7149244707:ℚ)/15800000000),((3712706519:ℚ)/6675000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2711929477:ℚ)/5000000000),((4314660177155720429221756361881511:ℚ)/1872300000000000000000000000000000000),((-1815774937251005528161788067:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/16),((1:ℚ)/2),((674694261:ℚ)/1000000000),((1726060139:ℚ)/2500000000),((5170859827:ℚ)/11250000000),((1886060139:ℚ)/3456250000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((29896881:ℚ)/62500000),((501546235653674441011038236386999:ℚ)/316406250000000000000000000000000000),((-54881641654430853914610329:ℚ)/443596800000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((3432893271:ℚ)/5000000000),((3511532749:ℚ)/5000000000),((26270252897:ℚ)/57200000000),((425725861:ℚ)/781250000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((886358309:ℚ)/2000000000),((936650204845089382990844494228563:ℚ)/629200000000000000000000000000000000),((-1377182317481180210839001009:ℚ)/11089920000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((7:ℚ)/16),((1:ℚ)/2),((139692547:ℚ)/200000000),((3541238521:ℚ)/5000000000),((355815943:ℚ)/769000000),((3861238521:ℚ)/7150000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((4051839183:ℚ)/10000000000),((2580860892582011539418293171969:ℚ)/2217603750000000000000000000000000),((-737252180523576141454947:ℚ)/5914624000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((7044046631:ℚ)/10000000000),((7141887989:ℚ)/10000000000),((53788326417:ℚ)/116300000000),((2593962663:ℚ)/4806250000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3848673543:ℚ)/10000000000),((7610077243093717985238670862168027:ℚ)/6762845000000000000000000000000000000),((-1846586256438977653451964763:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((7:ℚ)/16),((1:ℚ)/2),((7103465187:ℚ)/10000000000),((450081147:ℚ)/625000000),((7743465187:ℚ)/16750000000),((490081147:ℚ)/908593750),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((726953097:ℚ)/2000000000),((1145414436720727130800384493640457:ℚ)/1052109375000000000000000000000000000),((-5550150436548318905537279081:ℚ)/44359680000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((7162883037:ℚ)/10000000000),((7260708147:ℚ)/10000000000),((54620181259:ℚ)/118200000000),((7900708147:ℚ)/14656250000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1704044341:ℚ)/5000000000),((18406649256023316094140294762397031:ℚ)/17464050000000000000000000000000000000),((-5560566358063210703621960681:ℚ)/44359680000000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((7:ℚ)/16),((1:ℚ)/2),((3611150099:ℚ)/5000000000),((3660058693:ℚ)/5000000000),((27518050693:ℚ)/59575000000),((1326686231:ℚ)/2462500000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1582948579:ℚ)/5000000000),((27180450146535489815460204533070551:ℚ)/26618854687500000000000000000000000000),((-464250544665266802398250883:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((3640858343:ℚ)/5000000000),((7379526083:ℚ)/10000000000),((27726008401:ℚ)/60050000000),((8019526083:ℚ)/14893750000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2904307367:ℚ)/10000000000),((2231232110032175735130563741287113:ℚ)/2253751562500000000000000000000000000),((-465122581023455672275061467:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((1835283129:ℚ)/2500000000),((3749170951:ℚ)/5000000000),((13966981903:ℚ)/30500000000),((4069170951:ℚ)/7506250000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((654376147:ℚ)/2500000000),((2754566833232814990696395079747977:ℚ)/2325625000000000000000000000000000000),((-349497479298794838594489809:ℚ)/2772480000000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((1864990567:ℚ)/2500000000),((7735967569:ℚ)/10000000000),((14174933969:ℚ)/31450000000),((8375967569:ℚ)/15250000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((961324177:ℚ)/5000000000),((113006960189211308439465564028661:ℚ)/72728125000000000000000000000000000),((-116937705226280275547572187:ℚ)/924160000000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((7697614537:ℚ)/10000000000),((3986792931:ℚ)/5000000000),((58363301759:ℚ)/129600000000),((4306792931:ℚ)/7862500000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((60616214857183982741132899925593969:ℚ)/41990400000000000000000000000000000000),((-130146401:ℚ)/1024000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((7935257869:ℚ)/10000000000),((2468582453:ℚ)/2500000000),((60026805083:ℚ)/160000000000),((292064717:ℚ)/450000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((275893930210649757015403421968892123:ℚ)/48000000000000000000000000000000000000),((-130146401:ℚ)/1024000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((491807963:ℚ)/500000000),((1709400367:ℚ)/1250000000),((3666655741:ℚ)/11040000000),((1789400367:ℚ)/2500000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((308245625873339284467059:ℚ)/30470400000000000000000000),((-130146401:ℚ)/1024000000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound ninth nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC24
#check @N11Formalization.C450NinthGroupedC24.bound
#print axioms N11Formalization.C450NinthGroupedC24.valid0
#print axioms N11Formalization.C450NinthGroupedC24.valid1
#print axioms N11Formalization.C450NinthGroupedC24.valid2
#print axioms N11Formalization.C450NinthGroupedC24.valid3
#print axioms N11Formalization.C450NinthGroupedC24.valid4
#print axioms N11Formalization.C450NinthGroupedC24.valid5
#print axioms N11Formalization.C450NinthGroupedC24.valid6
#print axioms N11Formalization.C450NinthGroupedC24.valid7
#print axioms N11Formalization.C450NinthGroupedC24.valid8
#print axioms N11Formalization.C450NinthGroupedC24.valid9
#print axioms N11Formalization.C450NinthGroupedC24.valid10
#print axioms N11Formalization.C450NinthGroupedC24.valid11
#print axioms N11Formalization.C450NinthGroupedC24.valid12
#print axioms N11Formalization.C450NinthGroupedC24.valid13
#print axioms N11Formalization.C450NinthGroupedC24.valid14
#print axioms N11Formalization.C450NinthGroupedC24.bound
#print axioms N11Formalization.C450NinthGroupedC24.endpoint_checks
