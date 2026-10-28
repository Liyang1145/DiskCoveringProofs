import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((3147672791:ℚ)/5000000000),((6571332127:ℚ)/10000000000),((-5163332127:ℚ)/19840000000),((-2187672791:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5946672811:ℚ)/10000000000),((10955730587013256094502243328635715183612047162158241307:ℚ)/248104519042968750000000000000000000000000000000000000000),((33963385452575892997850241:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((6533387441:ℚ)/10000000000),((170235219:ℚ)/250000000),((-135035219:ℚ)/515000000),((-4613387441:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5361999191:ℚ)/10000000000),((26863000619343589753641580039553684629058961228137638807:ℚ)/612662121562500000000000000000000000000000000000000000000),((20136529455370764320369:ℚ)/462080000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((3385695309:ℚ)/5000000000),((1385686381:ℚ)/2000000000),((-1104086381:ℚ)/4272000000),((-2425695309:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2356569741:ℚ)/5000000000),((35997106625466118470095400578108078061348730162944888527:ℚ)/837220677004394531250000000000000000000000000000000000000),((1218050894559411933072169:ℚ)/29573120000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((3445189487:ℚ)/5000000000),((1746984979:ℚ)/2500000000),((-1394984979:ℚ)/5435000000),((-2485189487:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((1088930207:ℚ)/2500000000),((12420345267479289411762292611557851688021893160251462483:ℚ)/291550813877334594726562500000000000000000000000000000000),((1847996137475469873677289:ℚ)/46208000000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((1389974009:ℚ)/2000000000),((1409489127:ℚ)/2000000000),((-1127889127:ℚ)/4386000000),((-1005974009:ℚ)/5530000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4166332637:ℚ)/10000000000),((102746899430463740595670365953556399348328836089002659:ℚ)/2414475538808593750000000000000000000000000000000000000),((1165296516763210718312241:ℚ)/29573120000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((1752339779:ℚ)/2500000000),((7106949119:ℚ)/10000000000),((-5698949119:ℚ)/22120000000),((-1272339779:ℚ)/6971875000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((158738961:ℚ)/400000000),((622378994797660315722227689329302893633689688809629867:ℚ)/14640770655210018157958984375000000000000000000000000000),((28697005118999076335743169:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((7068846239:ℚ)/10000000000),((7166450427:ℚ)/10000000000),((-5758450427:ℚ)/22310000000),((-5148846239:ℚ)/28125000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1880402149:ℚ)/5000000000),((30876110209291541166946975659638586269292378414498903803:ℚ)/727057009935379028320312500000000000000000000000000000000),((28261714408766246959758041:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((7128331463:ℚ)/10000000000),((7225949613:ℚ)/10000000000),((-5817949613:ℚ)/22500000000),((-5208331463:ℚ)/28362500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((22134961:ℚ)/62500000),((27224559100337844685520892518182163581805610050577023:ℚ)/641691161993408203125000000000000000000000000000000000),((27826540419717151872293801:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((1796953709:ℚ)/2500000000),((728544673:ℚ)/1000000000),((-587744673:ℚ)/2269000000),((-1316953709:ℚ)/7150000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((4135681:ℚ)/12500000),((43943554601298753316619001266259493378771334041756715489:ℚ)/1036722762968750000000000000000000000000000000000000000000),((273914827908741317501441:ℚ)/7393280000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((1811824101:ℚ)/2500000000),((7344941829:ℚ)/10000000000),((-456687833:ℚ)/1760000000),((-443941367:ℚ)/2403125000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1529245463:ℚ)/5000000000),((86092891562135914979190013850456147247252589519:ℚ)/2032920460402965545654296875000000000000000000000),((26956541176249211228086489:ℚ)/739328000000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((7306776213:ℚ)/10000000000),((7404434961:ℚ)/10000000000),((-5996434961:ℚ)/23070000000),((-5386776213:ℚ)/29075000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2786853353:ℚ)/10000000000),((2999122447430960674046164687142094233494912078177660355399:ℚ)/70878868795488281250000000000000000000000000000000000000000),((26521715230207452950128609:ℚ)/739328000000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((230195447:ℚ)/312500000),((752341551:ℚ)/1000000000),((-611541551:ℚ)/2326000000),((-170195447:ℚ)/923437500),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((49731257:ℚ)/200000000),((450915909235074932899426042508770965290812130453883:ℚ)/10599575995206832885742187500000000000000000000000000),((260999585120387270296929:ℚ)/7393280000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((7485205503:ℚ)/10000000000),((7761355007:ℚ)/10000000000),((-6353355007:ℚ)/23640000000),((-5565205503:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((870135551:ℚ)/5000000000),((900747433894394413937035074725959546827414032122493299993:ℚ)/20960276718750000000000000000000000000000000000000000000000),((33186447013151257:ℚ)/972800000000000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((1544617811:ℚ)/2000000000),((8237156487:ℚ)/10000000000),((-6829156487:ℚ)/24400000000),((-1160617811:ℚ)/6480000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((302659218021145144867281767623623379909495286298035773:ℚ)/6915818880000000000000000000000000000000000000000000000),((8434173:ℚ)/256000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((1639757707:ℚ)/2000000000),((5069799797:ℚ)/5000000000),((-1455266599:ℚ)/4320000000),((-1255757707:ℚ)/8000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((832084255414278529616913166725438562106712500445694369:ℚ)/17280000000000000000000000000000000000000000000000000000),((8434173:ℚ)/256000000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((2525230219:ℚ)/2500000000),((13942465337:ℚ)/10000000000),((-12534465337:ℚ)/32000000000),((-88923053:ℚ)/600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((10973445040809553759789367845724897444750506401319:ℚ)/202500000000000000000000000000000000000000000000000),((8434173:ℚ)/256000000)⟩
theorem valid15 : Valid source13 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source13 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source13 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source13 nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC12
#check @N11Formalization.C450Source13GroupedC12.bound
#print axioms N11Formalization.C450Source13GroupedC12.valid0
#print axioms N11Formalization.C450Source13GroupedC12.valid1
#print axioms N11Formalization.C450Source13GroupedC12.valid2
#print axioms N11Formalization.C450Source13GroupedC12.valid3
#print axioms N11Formalization.C450Source13GroupedC12.valid4
#print axioms N11Formalization.C450Source13GroupedC12.valid5
#print axioms N11Formalization.C450Source13GroupedC12.valid6
#print axioms N11Formalization.C450Source13GroupedC12.valid7
#print axioms N11Formalization.C450Source13GroupedC12.valid8
#print axioms N11Formalization.C450Source13GroupedC12.valid9
#print axioms N11Formalization.C450Source13GroupedC12.valid10
#print axioms N11Formalization.C450Source13GroupedC12.valid11
#print axioms N11Formalization.C450Source13GroupedC12.valid12
#print axioms N11Formalization.C450Source13GroupedC12.valid13
#print axioms N11Formalization.C450Source13GroupedC12.valid14
#print axioms N11Formalization.C450Source13GroupedC12.valid15
#print axioms N11Formalization.C450Source13GroupedC12.bound
#print axioms N11Formalization.C450Source13GroupedC12.endpoint_checks
