import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC16
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((-1:ℚ)/16),(0:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/16),(0:ℚ),((3085449723:ℚ)/5000000000),((668655997:ℚ)/1000000000),((2554427:ℚ)/120000000),((3:ℚ)/31),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3116467101:ℚ)/5000000000),((1409826317181213135430043:ℚ)/26811900000000000000000000),((-8864192870453223:ℚ)/97280000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((3323989507:ℚ)/5000000000),((432804251:ℚ)/625000000),((127195749:ℚ)/6912500000),((8:ℚ)/89),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1011819037:ℚ)/2000000000),((3215707862121672712071422408628760752953:ℚ)/63159921363574218750000000000000000000000),((-9759790728021007:ℚ)/97280000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/16),(0:ℚ),((3443205491:ℚ)/5000000000),((7044001469:ℚ)/10000000000),((638666177:ℚ)/37500000000),((48:ℚ)/553),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4368078639:ℚ)/10000000000),((1067259670223094631281553971928978913928487:ℚ)/21233417871093750000000000000000000000000000),((-10207387259164991:ℚ)/97280000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/16),(0:ℚ),((875700403:ℚ)/1250000000),((7103563357:ℚ)/10000000000),((1856436643:ℚ)/113450000000),((32:ℚ)/375),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1990620307:ℚ)/5000000000),((271372103255711330590318345326854565899:ℚ)/5429911992187500000000000000000000000000),((-2607785238763903:ℚ)/24320000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/16),(0:ℚ),((7065193759:ℚ)/10000000000),((57304977:ℚ)/80000000),((1105771:ℚ)/70400000),((192:ℚ)/2269),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3773867873:ℚ)/10000000000),((360918093958112076493826730339326204237:ℚ)/7237004104647680000000000000000000000000),((-21086014633359259:ℚ)/194560000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/16),(0:ℚ),((890597587:ℚ)/1250000000),((3611338927:ℚ)/5000000000),((289553691:ℚ)/19225000000),((12:ℚ)/143),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3555041151:ℚ)/10000000000),((1293055565310042692643523080701788399119:ℚ)/25980498433398437500000000000000000000000),((-2663716730989087:ℚ)/24320000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((7184364123:ℚ)/10000000000),((910278827:ℚ)/1250000000),((209721173:ℚ)/14537500000),((64:ℚ)/769),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((26579947:ℚ)/80000000),((596759661344772081463310015093308014607909:ℚ)/12013470544502363281250000000000000000000000),((-21533439884167623:ℚ)/194560000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((113186627:ℚ)/156250000),((7401327531:ℚ)/10000000000),((1558672469:ℚ)/118200000000),((96:ℚ)/1163),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1536553107:ℚ)/5000000000),((37876447013088826214737709410065395006095479:ℚ)/763100274041537500000000000000000000000000000),((-339955204258127:ℚ)/3040000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((7363094201:ℚ)/10000000000),((3760206711:ℚ)/5000000000),((719793289:ℚ)/60050000000),((16:ℚ)/197),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2503402587:ℚ)/10000000000),((2556936088857233999030362284517967473311361:ℚ)/51692314033935937500000000000000000000000000),((-22204482140748701:ℚ)/194560000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-1:ℚ)/16),(0:ℚ),((3741115777:ℚ)/5000000000),((954936101:ℚ)/1250000000),((165063899:ℚ)/15250000000),((96:ℚ)/1201),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1762727127:ℚ)/10000000000),((12416502727070100645613164022854682442324999:ℚ)/251795942160976562500000000000000000000000000),((-11325891725862277:ℚ)/97280000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/16),(0:ℚ),((475084799:ℚ)/625000000),((8115694589:ℚ)/10000000000),((281435137:ℚ)/43200000000),((24:ℚ)/305),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((6544832431885688812043841084223240392479:ℚ)/132375319200000000000000000000000000000000),((-3038677:ℚ)/25600000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/16),(0:ℚ),((1009718401:ℚ)/1250000000),((2504888553:ℚ)/2500000000),((-264888553:ℚ)/32400000000),((2:ℚ)/27),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((57557346136591809991902937:ℚ)/1153300781250000000000000000),((-3038677:ℚ)/25600000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/16),(0:ℚ),((1247747971:ℚ)/1250000000),((13824501353:ℚ)/10000000000),((-4864501353:ℚ)/160000000000),((3:ℚ)/50),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((8794380911277119:ℚ)/160000000000000000),((-3038677:ℚ)/25600000)⟩
theorem valid12 : Valid source16 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source16 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source16 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source16 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC16
#check @N11Formalization.C450Source16GroupedC16.bound
#print axioms N11Formalization.C450Source16GroupedC16.valid0
#print axioms N11Formalization.C450Source16GroupedC16.valid1
#print axioms N11Formalization.C450Source16GroupedC16.valid2
#print axioms N11Formalization.C450Source16GroupedC16.valid3
#print axioms N11Formalization.C450Source16GroupedC16.valid4
#print axioms N11Formalization.C450Source16GroupedC16.valid5
#print axioms N11Formalization.C450Source16GroupedC16.valid6
#print axioms N11Formalization.C450Source16GroupedC16.valid7
#print axioms N11Formalization.C450Source16GroupedC16.valid8
#print axioms N11Formalization.C450Source16GroupedC16.valid9
#print axioms N11Formalization.C450Source16GroupedC16.valid10
#print axioms N11Formalization.C450Source16GroupedC16.valid11
#print axioms N11Formalization.C450Source16GroupedC16.valid12
#print axioms N11Formalization.C450Source16GroupedC16.bound
#print axioms N11Formalization.C450Source16GroupedC16.endpoint_checks
