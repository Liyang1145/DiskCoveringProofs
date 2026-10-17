import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((3171395879:ℚ)/5000000000),((6626533821:ℚ)/10000000000),((-15719601463:ℚ)/49600000000),((-2275395879:ℚ)/10300000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1458575673:ℚ)/2500000000),((11323019748671237459823844537413064680064863725940796791:ℚ)/211715856250000000000000000000000000000000000000000000000),((57466620251276200229701139:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((131620421:ℚ)/200000000),((3432391059:ℚ)/5000000000),((-8217173177:ℚ)/25750000000),((-31926807:ℚ)/142400000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5238019029:ℚ)/10000000000),((24704337889400200809036370824323132383309926074751:ℚ)/464715564800000000000000000000000000000000000000000),((88361127326324102934539:ℚ)/1182924800000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((3409599111:ℚ)/5000000000),((3491943279:ℚ)/5000000000),((-8395829837:ℚ)/26700000000),((-2513599111:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((142895609:ℚ)/312500000),((111408680624190187709246404538054675621944565330040703963:ℚ)/2143284933131250000000000000000000000000000000000000000000),((52981664588039127261307859:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((6938268981:ℚ)/10000000000),((7043434151:ℚ)/10000000000),((-16970302453:ℚ)/54350000000),((-5146268981:ℚ)/21930000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((168155721:ℚ)/400000000),((34120366517828795872611130717351137131888862775143062719:ℚ)/663440074245312500000000000000000000000000000000000000000),((207433830007990487994463019:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((279912007:ℚ)/400000000),((7102978767:ℚ)/10000000000),((-17148936301:ℚ)/54825000000),((-208232007:ℚ)/884800000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2003820369:ℚ)/5000000000),((7622909008566734509117340137597469480345611989115289:ℚ)/148345377104400000000000000000000000000000000000000000),((328297950360829024428371:ℚ)/4731699200000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((1764332169:ℚ)/2500000000),((3581260241:ℚ)/5000000000),((-8663780723:ℚ)/27650000000),((-1316332169:ℚ)/5577500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3801853263:ℚ)/10000000000),((1924416409973378953456517970960159078007564648195217367:ℚ)/37480372877337646484375000000000000000000000000000000000),((12683612908024882109792819:ℚ)/184832000000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((889606819:ℚ)/1250000000),((7222059369:ℚ)/10000000000),((-17506178107:ℚ)/55775000000),((-665606819:ℚ)/2812500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1792442307:ℚ)/5000000000),((20723009110768970484428118653773414360347638716508177:ℚ)/403920561075210571289062500000000000000000000000000000),((3135759222175945100574619:ℚ)/46208000000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((717637787:ℚ)/1000000000),((7281595501:ℚ)/10000000000),((-17684786503:ℚ)/56250000000),((-538437787:ℚ)/2269000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((167728071:ℚ)/500000000),((84216553203630323300575359827142297312166002491717:ℚ)/1642729374703125000000000000000000000000000000000000),((1984385676344120955784651:ℚ)/29573120000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((1447179739:ℚ)/2000000000),((1468225789:ℚ)/2000000000),((-3572677367:ℚ)/11345000000),((-1088779739:ℚ)/4576000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1553955607:ℚ)/5000000000),((69613115010427846139689027968079661621274553857169512409:ℚ)/1358853259878400000000000000000000000000000000000000000000),((7847509457269450931114059:ℚ)/118292480000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((729541709:ℚ)/1000000000),((740065977:ℚ)/1000000000),((-1804197931:ℚ)/5720000000),((-550341709:ℚ)/2307000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((355084881:ℚ)/1250000000),((7315016371292670524396668258548101170438229582959:ℚ)/142888612251708984375000000000000000000000000000000),((1939360943408449553786299:ℚ)/29573120000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((3677466557:ℚ)/5000000000),((7460188039:ℚ)/10000000000),((-18220564117:ℚ)/57675000000),((-2781466557:ℚ)/11630000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2546387467:ℚ)/10000000000),((1160366985696913714753041699539298394965760189836126984001:ℚ)/22681238014556250000000000000000000000000000000000000000000),((47920909809734579954558171:ℚ)/739328000000000000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((7414446827:ℚ)/10000000000),((3789618579:ℚ)/5000000000),((-9288855737:ℚ)/29075000000),((-5622446827:ℚ)/23640000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2214266967:ℚ)/10000000000),((45819807144802114526012973670534055899796596021570337653:ℚ)/889156879900000000000000000000000000000000000000000000000),((189430368961763773308118891:ℚ)/2957312000000000000000000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((7533467539:ℚ)/10000000000),((1563461469:ℚ)/2000000000),((-3858384407:ℚ)/11820000000),((-5741467539:ℚ)/24400000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1324165699:ℚ)/10000000000),((2802937403669842986235234343704579717222652696916980729891:ℚ)/53658308400000000000000000000000000000000000000000000000000),((184921375002265065414177659:ℚ)/2957312000000000000000000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((3885741793:ℚ)/5000000000),((4146673541:ℚ)/5000000000),((-10360020623:ℚ)/30500000000),((-2989741793:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1644760357181033593623838252725482312909044455345507889:ℚ)/30736972800000000000000000000000000000000000000000000000),((12631529:ℚ)/204800000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((4123712313:ℚ)/5000000000),((10196515911:ℚ)/10000000000),((-26429547733:ℚ)/64800000000),((-3227712313:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((124917345658886985290351270539252407182473919313827085463:ℚ)/2073600000000000000000000000000000000000000000000000000000),((12631529:ℚ)/204800000)⟩
theorem valid14 : Valid source15 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((10150292859:ℚ)/10000000000),((14000232053:ℚ)/10000000000),((-37840696159:ℚ)/80000000000),((-8358292859:ℚ)/44160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1023446508218654209032470672548304308013375499023217949:ℚ)/14950809600000000000000000000000000000000000000000000000),((12631529:ℚ)/204800000)⟩
theorem valid15 : Valid source15 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source15 nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC11
#check @N11Formalization.C450Source15GroupedC11.bound
#print axioms N11Formalization.C450Source15GroupedC11.valid0
#print axioms N11Formalization.C450Source15GroupedC11.valid1
#print axioms N11Formalization.C450Source15GroupedC11.valid2
#print axioms N11Formalization.C450Source15GroupedC11.valid3
#print axioms N11Formalization.C450Source15GroupedC11.valid4
#print axioms N11Formalization.C450Source15GroupedC11.valid5
#print axioms N11Formalization.C450Source15GroupedC11.valid6
#print axioms N11Formalization.C450Source15GroupedC11.valid7
#print axioms N11Formalization.C450Source15GroupedC11.valid8
#print axioms N11Formalization.C450Source15GroupedC11.valid9
#print axioms N11Formalization.C450Source15GroupedC11.valid10
#print axioms N11Formalization.C450Source15GroupedC11.valid11
#print axioms N11Formalization.C450Source15GroupedC11.valid12
#print axioms N11Formalization.C450Source15GroupedC11.valid13
#print axioms N11Formalization.C450Source15GroupedC11.valid14
#print axioms N11Formalization.C450Source15GroupedC11.valid15
#print axioms N11Formalization.C450Source15GroupedC11.bound
#print axioms N11Formalization.C450Source15GroupedC11.endpoint_checks
