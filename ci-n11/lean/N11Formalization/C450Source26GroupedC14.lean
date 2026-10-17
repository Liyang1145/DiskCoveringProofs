import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((3122550039:ℚ)/5000000000),((6549619343:ℚ)/10000000000),((-138350259:ℚ)/3200000000),((877449961:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6063672409:ℚ)/10000000000),((674464739942038440611828559585298813:ℚ)/3813248000000000000000000000000000000),((-5404282606308185962268303:ℚ)/27724800000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((1621396047:ℚ)/2500000000),((424364469:ℚ)/625000000),((-313093407:ℚ)/6437500000),((378603953:ℚ)/12875000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5483873199:ℚ)/10000000000),((9137406860152192608822579336150125946583390212655527:ℚ)/52105283737182617187500000000000000000000000000000000),((-1443781731455604253601087:ℚ)/6931200000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((1345170443:ℚ)/2000000000),((6909865309:ℚ)/10000000000),((-1789865309:ℚ)/35600000000),((254829557:ℚ)/10680000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4843440793:ℚ)/10000000000),((3949673239510635794002948675031087577214480090254341921:ℚ)/22840995600000000000000000000000000000000000000000000000),((-327851980646975966656269:ℚ)/1478656000000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((171147811:ℚ)/250000000),((878731789:ℚ)/1250000000),((-716195367:ℚ)/13587500000),((28852189:ℚ)/1358750000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4492387647:ℚ)/10000000000),((506970701521285040262995603349686653945631347711057:ℚ)/2939679343414306640625000000000000000000000000000000),((-5278127868098967542301:ℚ)/23104000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((6965926927:ℚ)/10000000000),((714980083:ℚ)/1000000000),((-608940249:ℚ)/11060000000),((1034073073:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((822762683:ℚ)/2000000000),((25979632215951565604840211104573277350896263725226688361:ℚ)/150993193750000000000000000000000000000000000000000000000),((-24083497495975809298509:ℚ)/102400000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((177147451:ℚ)/250000000),((7269707021:ℚ)/10000000000),((-716569007:ℚ)/12500000000),((22852549:ℚ)/1406250000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((924808759:ℚ)/2500000000),((2984564606118845287748246266397102585252096968143299:ℚ)/17380714416503906250000000000000000000000000000000000),((-5589823660789365934381:ℚ)/23104000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((3602913993:ℚ)/5000000000),((7389574899:ℚ)/10000000000),((-6808724697:ℚ)/114400000000),((397086007:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3234791179:ℚ)/10000000000),((1708963175732088184725128204492102977870462433035730201:ℚ)/9968887500000000000000000000000000000000000000000000000),((-6895300804915617208064207:ℚ)/27724800000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((366285941:ℚ)/500000000),((3754703173:ℚ)/5000000000),((-3584109519:ℚ)/58150000000),((33714059:ℚ)/2907500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1347383011:ℚ)/5000000000),((19723533516277842105609063370249578914661507392641727:ℚ)/115212725610351562500000000000000000000000000000000000),((-23610489997422032430861:ℚ)/92416000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((1489114493:ℚ)/2000000000),((3874483437:ℚ)/5000000000),((-1314483437:ℚ)/19700000000),((110885507:ℚ)/11820000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((504834143:ℚ)/2500000000),((5330050610583020760269620637613691110668381228443042751:ℚ)/30963760650000000000000000000000000000000000000000000000),((-1074249988830896204629:ℚ)/4096000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((384258763:ℚ)/500000000),((8227721159:ℚ)/10000000000),((-9323163477:ℚ)/122000000000),((15741237:ℚ)/3050000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((7715938740631311526287000498833176380830779343981707:ℚ)/44332226562500000000000000000000000000000000000000000),((-17346211:ℚ)/64000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((8163805067:ℚ)/10000000000),((2027828177:ℚ)/2000000000),((-1003828177:ℚ)/8640000000),((-163805067:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((16093647392402401203889292126068667633944366241410882483889:ℚ)/86400000000000000000000000000000000000000000000000000000000),((-17346211:ℚ)/64000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((2518634163:ℚ)/2500000000),((2790499501:ℚ)/2000000000),((-5299498503:ℚ)/32000000000),((-518634163:ℚ)/27600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((20901849502918275749719735937986570344776779796459149769:ℚ)/98552700000000000000000000000000000000000000000000000000),((-17346211:ℚ)/64000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC14
#check @N11Formalization.C450Source26GroupedC14.bound
#print axioms N11Formalization.C450Source26GroupedC14.valid0
#print axioms N11Formalization.C450Source26GroupedC14.valid1
#print axioms N11Formalization.C450Source26GroupedC14.valid2
#print axioms N11Formalization.C450Source26GroupedC14.valid3
#print axioms N11Formalization.C450Source26GroupedC14.valid4
#print axioms N11Formalization.C450Source26GroupedC14.valid5
#print axioms N11Formalization.C450Source26GroupedC14.valid6
#print axioms N11Formalization.C450Source26GroupedC14.valid7
#print axioms N11Formalization.C450Source26GroupedC14.valid8
#print axioms N11Formalization.C450Source26GroupedC14.valid9
#print axioms N11Formalization.C450Source26GroupedC14.valid10
#print axioms N11Formalization.C450Source26GroupedC14.valid11
#print axioms N11Formalization.C450Source26GroupedC14.bound
#print axioms N11Formalization.C450Source26GroupedC14.endpoint_checks
