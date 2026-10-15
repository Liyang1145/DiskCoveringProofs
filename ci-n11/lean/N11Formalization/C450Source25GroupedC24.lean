import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((2832002603:ℚ)/5000000000),((3110518081:ℚ)/5000000000),((9061339407:ℚ)/17800000000),((4070518081:ℚ)/6200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3649329351:ℚ)/5000000000),((-65723451761907118433212832313414199:ℚ)/1409938000000000000000000000000000000),((-280614377951888802137503:ℚ)/722000000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((767877793:ℚ)/1250000000),((646031739:ℚ)/1000000000),((7215144551:ℚ)/13825000000),((279343913:ℚ)/445000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((196734443:ℚ)/312500000),((-1012240253467438437780369068978132252378374673224642709:ℚ)/16514880566406250000000000000000000000000000000000000000),((-34379150666471699448149:ℚ)/86640000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/16),((1:ℚ)/2),((6382321489:ℚ)/10000000000),((1315982479:ℚ)/2000000000),((19798750141:ℚ)/37500000000),((1699982479:ℚ)/2765000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((358700013:ℚ)/625000000),((-7449102591528539758630757594274889794408599385063111997:ℚ)/109863281250000000000000000000000000000000000000000000000),((-46301676723759066671743:ℚ)/115520000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((6501924987:ℚ)/10000000000),((1308492:ℚ)/1953125),((60233474909:ℚ)/114400000000),((17957248:ℚ)/29296875),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1088497753:ℚ)/2000000000),((-5238066767551139471038719145461044998296113172305598559:ℚ)/77334400000000000000000000000000000000000000000000000000),((-57239620643398803613:ℚ)/142500000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((6621499839:ℚ)/10000000000),((426188671:ℚ)/625000000),((61070498873:ℚ)/116300000000),((546188671:ℚ)/893750000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2565265599:ℚ)/5000000000),((-166214054877768792724204757525345098045946220776359035323:ℚ)/2457871479687500000000000000000000000000000000000000000000),((-9081675262046215790911:ℚ)/22562500000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((6741047467:ℚ)/10000000000),((3469266399:ℚ)/5000000000),((20635777423:ℚ)/39400000000),((4429266399:ℚ)/7268750000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4800324669:ℚ)/10000000000),((-6449118583008889441144544381525456691303904756443516637:ℚ)/95567162500000000000000000000000000000000000000000000000),((-873552295649151595124669:ℚ)/2166000000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((3430284601:ℚ)/5000000000),((3529011229:ℚ)/5000000000),((31371992207:ℚ)/60050000000),((4489011229:ℚ)/7387500000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4447773747:ℚ)/10000000000),((-91090938961232357522842863667623866856208864467347947397:ℚ)/1353377813281250000000000000000000000000000000000000000000),((-291725574278492633286743:ℚ)/722000000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((436254143:ℚ)/625000000),((7177488871:ℚ)/10000000000),((3973779001:ℚ)/7625000000),((9097488871:ℚ)/15012500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((203351849:ℚ)/500000000),((-185912740523473824759468769902319566091399420839534899:ℚ)/2770764160156250000000000000000000000000000000000000000),((-1168952238917367994783343:ℚ)/2888000000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((7099539891:ℚ)/10000000000),((7416356217:ℚ)/10000000000),((64416779237:ℚ)/125800000000),((9336356217:ℚ)/15250000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((114039539:ℚ)/312500000),((-191105244726391384429480078681191548637891323737788715687:ℚ)/3110727362500000000000000000000000000000000000000000000000),((-3491343470633894450739341:ℚ)/8664000000000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((3669210477:ℚ)/5000000000),((306205709:ℚ)/400000000),((33044473339:ℚ)/64800000000),((383005709:ℚ)/629000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((526251381:ℚ)/2000000000),((-427506374004310037655955250286796815765885327768917563:ℚ)/6998400000000000000000000000000000000000000000000000000),((-3080198367715429:ℚ)/7600000000000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((3788610181:ℚ)/5000000000),((2390805391:ℚ)/2500000000),((33880271267:ℚ)/80000000000),((2870805391:ℚ)/4050000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((77444423:ℚ)/1000000000),((-2966837203455124816006535615460769:ℚ)/500000000000000000000000000000000000),((-3127143585135037:ℚ)/7600000000000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((9485380071:ℚ)/10000000000),((13372680809:ℚ)/10000000000),((81117660497:ℚ)/220800000000),((15292680809:ℚ)/20000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((69266931680060767646468941:ℚ)/1523520000000000000000000000),((-824111:ℚ)/2000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source25 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source25 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC24
#check @N11Formalization.C450Source25GroupedC24.bound
#print axioms N11Formalization.C450Source25GroupedC24.valid0
#print axioms N11Formalization.C450Source25GroupedC24.valid1
#print axioms N11Formalization.C450Source25GroupedC24.valid2
#print axioms N11Formalization.C450Source25GroupedC24.valid3
#print axioms N11Formalization.C450Source25GroupedC24.valid4
#print axioms N11Formalization.C450Source25GroupedC24.valid5
#print axioms N11Formalization.C450Source25GroupedC24.valid6
#print axioms N11Formalization.C450Source25GroupedC24.valid7
#print axioms N11Formalization.C450Source25GroupedC24.valid8
#print axioms N11Formalization.C450Source25GroupedC24.valid9
#print axioms N11Formalization.C450Source25GroupedC24.valid10
#print axioms N11Formalization.C450Source25GroupedC24.valid11
#print axioms N11Formalization.C450Source25GroupedC24.bound
#print axioms N11Formalization.C450Source25GroupedC24.endpoint_checks
