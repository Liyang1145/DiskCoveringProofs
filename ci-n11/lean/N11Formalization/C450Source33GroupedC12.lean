import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((6392639227:ℚ)/10000000000),((825082673:ℚ)/1250000000),((-329082673:ℚ)/2480000000),((-1272639227:ℚ)/25275000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2857073271:ℚ)/5000000000),((5025951377031680913424483371690979:ℚ)/59582000000000000000000000000000000),((-3806297684318625321041741:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((3256818077:ℚ)/5000000000),((3360815017:ℚ)/5000000000),((-458938339:ℚ)/3370000000),((-696818077:ℚ)/12875000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((5412654361:ℚ)/10000000000),((128958160170228930500110390332775482641780148585523:ℚ)/1495029414062500000000000000000000000000000000000000),((-1369436964736970472423341:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((3317273953:ℚ)/5000000000),((6842516131:ℚ)/10000000000),((-2874516131:ℚ)/20600000000),((-757273953:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((254772201:ℚ)/500000000),((1879838652325378949845505457505196082266501850408963:ℚ)/21342324218750000000000000000000000000000000000000000),((-1790402910129122310091461:ℚ)/57760000000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((6755379277:ℚ)/10000000000),((6902929661:ℚ)/10000000000),((-2934929661:ℚ)/20980000000),((-1635379277:ℚ)/26462500000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((475932877:ℚ)/1000000000),((506946070117045434089068993263606200208031657496210853:ℚ)/5771603245000000000000000000000000000000000000000000000),((-8857927889387772524632541:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((340788311:ℚ)/500000000),((1740831059:ℚ)/2500000000),((-748831059:ℚ)/5292500000),((-84788311:ℚ)/1335000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((916575451:ℚ)/2000000000),((2054760404695915367326300107242150970697510951165923:ℚ)/23163417023925781250000000000000000000000000000000000),((-24276917609109069300509:ℚ)/577600000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/16),((-1:ℚ)/4),((1375226941:ℚ)/2000000000),((877962547:ℚ)/1250000000),((-127320849:ℚ)/890000000),((-351226941:ℚ)/5387500000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4399931841:ℚ)/10000000000),((39461836560798945431844269070673417994224743326793:ℚ)/440605625000000000000000000000000000000000000000000),((-422669303204372068479549:ℚ)/9241600000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((3468242619:ℚ)/5000000000),((354202929:ℚ)/500000000),((-155802929:ℚ)/1077500000),((-908242619:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2104820111:ℚ)/5000000000),((70682171476742764868349568951658581657285388717857:ℚ)/781865146484375000000000000000000000000000000000000),((-2856457152392539278346269:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((54662643:ℚ)/78125000),((223262479:ℚ)/312500000),((-99262479:ℚ)/679375000),((-58650572:ℚ)/856640625),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((501368883:ℚ)/1250000000),((1117392609905590078340666051307191403373437254127:ℚ)/12248663930892944335937500000000000000000000000000),((-3000014418098660315559:ℚ)/56406250000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((1764283593:ℚ)/2500000000),((7204723087:ℚ)/10000000000),((-3236723087:ℚ)/21930000000),((-484283593:ℚ)/6912500000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((76050843:ℚ)/200000000),((14108395456447207350194459557915567845957543045777037:ℚ)/153294811875000000000000000000000000000000000000000000),((-822089232820596259750221:ℚ)/14440000000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((3558716947:ℚ)/5000000000),((7325321407:ℚ)/10000000000),((-3357321407:ℚ)/22120000000),((-332905649:ℚ)/4687500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((179135567:ℚ)/500000000),((91497008994623080142872855947698606074581522165608617:ℚ)/966356440000000000000000000000000000000000000000000000),((-3505484570033409179634861:ℚ)/57760000000000000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((7237985027:ℚ)/10000000000),((7445856941:ℚ)/10000000000),((-386428549:ℚ)/2500000000),((-2117985027:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1549460981:ℚ)/5000000000),((939343295016176196317321567335940427935000641882957:ℚ)/9765625000000000000000000000000000000000000000000000),((-15768399040801779859724541:ℚ)/231040000000000000000000000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((735847501:ℚ)/1000000000),((7927431503:ℚ)/10000000000),((-3959431503:ℚ)/22880000000),((-223847501:ℚ)/3050000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((2527819973:ℚ)/10000000000),((202535325310910832192910359412970194510177697264144199:ℚ)/1871492480000000000000000000000000000000000000000000000),((-175274681415245614119629:ℚ)/2310400000000000000000000)⟩
theorem valid11 : Valid source33 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source33 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((1567976427:ℚ)/2000000000),((8408220779:ℚ)/10000000000),((-4440220779:ℚ)/24400000000),((-543976427:ℚ)/6480000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((256036095650421648977095897688503511274566624608172763:ℚ)/2269810000000000000000000000000000000000000000000000000),((-11686531:ℚ)/128000000)⟩
theorem valid12 : Valid source33 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((332820973:ℚ)/400000000),((2581451189:ℚ)/2500000000),((-529817063:ℚ)/2160000000),((-128020973:ℚ)/1600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((180010528991340124803981188465883400149049961643653:ℚ)/1180980000000000000000000000000000000000000000000000),((-11686531:ℚ)/128000000)⟩
theorem valid13 : Valid source33 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((1279707921:ℚ)/1250000000),((7073165211:ℚ)/5000000000),((-5089165211:ℚ)/16000000000),((-639707921:ℚ)/6900000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((533474607916081649827886071285145993:ℚ)/2560000000000000000000000000000000000),((-11686531:ℚ)/128000000)⟩
theorem valid14 : Valid source33 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source33 nn0 nn1 Qcell ((1011:ℚ)/1600) ((1049:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source33 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source33 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC12
#check @N11Formalization.C450Source33GroupedC12.bound
#print axioms N11Formalization.C450Source33GroupedC12.valid0
#print axioms N11Formalization.C450Source33GroupedC12.valid1
#print axioms N11Formalization.C450Source33GroupedC12.valid2
#print axioms N11Formalization.C450Source33GroupedC12.valid3
#print axioms N11Formalization.C450Source33GroupedC12.valid4
#print axioms N11Formalization.C450Source33GroupedC12.valid5
#print axioms N11Formalization.C450Source33GroupedC12.valid6
#print axioms N11Formalization.C450Source33GroupedC12.valid7
#print axioms N11Formalization.C450Source33GroupedC12.valid8
#print axioms N11Formalization.C450Source33GroupedC12.valid9
#print axioms N11Formalization.C450Source33GroupedC12.valid10
#print axioms N11Formalization.C450Source33GroupedC12.valid11
#print axioms N11Formalization.C450Source33GroupedC12.valid12
#print axioms N11Formalization.C450Source33GroupedC12.valid13
#print axioms N11Formalization.C450Source33GroupedC12.valid14
#print axioms N11Formalization.C450Source33GroupedC12.bound
#print axioms N11Formalization.C450Source33GroupedC12.endpoint_checks
