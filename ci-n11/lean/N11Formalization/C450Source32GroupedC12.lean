import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((6390155989:ℚ)/10000000000),((1343263999:ℚ)/2000000000),((-575263999:ℚ)/3968000000),((-1430155989:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5720185279:ℚ)/10000000000),((16126593230003369678502590309179524053:ℚ)/165702647939072000000000000000000000000),((-2566571378675880207958119:ℚ)/115520000000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((6631777493:ℚ)/10000000000),((683707133:ℚ)/1000000000),((-299707133:ℚ)/2060000000),((-1671777493:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2551456121:ℚ)/5000000000),((4536453820533684145818773666289545898843659317647997081:ℚ)/46970229825273437500000000000000000000000000000000000000),((-4234306957154310474513511:ℚ)/115520000000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((3376236741:ℚ)/5000000000),((6897419387:ℚ)/10000000000),((-3057419387:ℚ)/20980000000),((-896236741:ℚ)/13231250000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((953533407:ℚ)/2000000000),((68215094386080936076734834934817317485751372395678775671207:ℚ)/708672076040570000000000000000000000000000000000000000000000),((-3807974577551274025272677:ℚ)/86640000000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((6812794647:ℚ)/10000000000),((434859357:ℚ)/625000000),((-194859357:ℚ)/1323125000),((-1852794647:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((2295853583:ℚ)/5000000000),((38359786721394907987876812207644327186789918032802313:ℚ)/395425487600250244140625000000000000000000000000000000),((-16503253357413278664531053:ℚ)/346560000000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/16),((-1:ℚ)/4),((3436549291:ℚ)/5000000000),((7018062791:ℚ)/10000000000),((-3178062791:ℚ)/21360000000),((-956549291:ℚ)/13468750000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4409301683:ℚ)/10000000000),((663574872847225716742330796333421767119474934848528736259241:ℚ)/6788745893842560000000000000000000000000000000000000000000000),((-1481599499828802756459959:ℚ)/28880000000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((6933385757:ℚ)/10000000000),((7078359089:ℚ)/10000000000),((-3238359089:ℚ)/21550000000),((-1973385757:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((843921841:ℚ)/2000000000),((1455516233575672923554707930705578606507783236440441389419613:ℚ)/14781241908262343750000000000000000000000000000000000000000000),((-6353241997628318382535511:ℚ)/115520000000000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((3496828313:ℚ)/5000000000),((446164941:ℚ)/625000000),((-206164941:ℚ)/1358750000),((-338942771:ℚ)/4568750000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((502699123:ℚ)/1250000000),((10386670289748420706304822282400248547061612661371038153:ℚ)/104723332908414154052734375000000000000000000000000000000),((-1695404576406628834567391:ℚ)/28880000000000000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((56431293:ℚ)/80000000),((2303649:ℚ)/3200000),((-358283:ℚ)/2339200),((-16751293:ℚ)/221200000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3813950853:ℚ)/10000000000),((11365234555143941392136454583428552388914196037:ℚ)/113787324491079680000000000000000000000000000000),((-1384613510949609256133:ℚ)/22179840000000000000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((3557075587:ℚ)/5000000000),((731938523:ℚ)/1000000000),((-347938523:ℚ)/2212000000),((-1077075587:ℚ)/14062500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((898752281:ℚ)/2500000000),((108915001677216465666680996672872084257181101202939:ℚ)/1064964240000000000000000000000000000000000000000000),((-1910743725521362980082791:ℚ)/28880000000000000000000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((3617292767:ℚ)/5000000000),((3719904289:ℚ)/5000000000),((-1799904289:ℚ)/11250000000),((-87484059:ℚ)/1100000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3113556273:ℚ)/10000000000),((22305641041238688513481912987388229730395419983326530437:ℚ)/215354003906250000000000000000000000000000000000000000000),((-2127620324235182525477871:ℚ)/28880000000000000000000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((735496279:ℚ)/1000000000),((1920122661:ℚ)/2500000000),((-960122661:ℚ)/5720000000),((-79832093:ℚ)/985000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((19892441:ℚ)/78125000),((245348521260590927409761169825803032465321958931048324393:ℚ)/2269710989260000000000000000000000000000000000000000000000),((-93841500944664975087199:ℚ)/1155200000000000000000000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((7595557293:ℚ)/10000000000),((7920970733:ℚ)/10000000000),((-4080970733:ℚ)/23640000000),((-2635557293:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((5342853:ℚ)/156250000),((20350624278997780815550406319807428244883792349733188037307:ℚ)/184345845405840000000000000000000000000000000000000000000000),((-33450063198540850594468133:ℚ)/346560000000000000000000000)⟩
theorem valid11 : Valid source32 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source32 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((3917977739:ℚ)/5000000000),((8401397697:ℚ)/10000000000),((-4561397697:ℚ)/24400000000),((-479325913:ℚ)/5400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((130795578055056373829955559454629175100236605789236199183:ℚ)/1103127660000000000000000000000000000000000000000000000000),((-6195499:ℚ)/64000000)⟩
theorem valid12 : Valid source32 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((8316233527:ℚ)/10000000000),((5158942753:ℚ)/5000000000),((-3238942753:ℚ)/12960000000),((-3356233527:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((79150207025756604743604407222122150275091521877266743:ℚ)/510183360000000000000000000000000000000000000000000000),((-6195499:ℚ)/64000000)⟩
theorem valid13 : Valid source32 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((5116135317:ℚ)/5000000000),((14137138407:ℚ)/10000000000),((-10297138407:ℚ)/32000000000),((-114614579:ℚ)/1200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1012911663152469332380904606622850171:ℚ)/4915200000000000000000000000000000000),((-6195499:ℚ)/64000000)⟩
theorem valid14 : Valid source32 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source32 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source32 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source32 nn0 nn1 Qcell ((2117:ℚ)/3200) ((2193:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source32 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source32 nn0 nn1 Qcell ((2193:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source32 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC12
#check @N11Formalization.C450Source32GroupedC12.bound
#print axioms N11Formalization.C450Source32GroupedC12.valid0
#print axioms N11Formalization.C450Source32GroupedC12.valid1
#print axioms N11Formalization.C450Source32GroupedC12.valid2
#print axioms N11Formalization.C450Source32GroupedC12.valid3
#print axioms N11Formalization.C450Source32GroupedC12.valid4
#print axioms N11Formalization.C450Source32GroupedC12.valid5
#print axioms N11Formalization.C450Source32GroupedC12.valid6
#print axioms N11Formalization.C450Source32GroupedC12.valid7
#print axioms N11Formalization.C450Source32GroupedC12.valid8
#print axioms N11Formalization.C450Source32GroupedC12.valid9
#print axioms N11Formalization.C450Source32GroupedC12.valid10
#print axioms N11Formalization.C450Source32GroupedC12.valid11
#print axioms N11Formalization.C450Source32GroupedC12.valid12
#print axioms N11Formalization.C450Source32GroupedC12.valid13
#print axioms N11Formalization.C450Source32GroupedC12.valid14
#print axioms N11Formalization.C450Source32GroupedC12.bound
#print axioms N11Formalization.C450Source32GroupedC12.endpoint_checks
