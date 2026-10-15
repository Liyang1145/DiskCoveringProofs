import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC23
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((3:ℚ)/8),((7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/8),((7:ℚ)/16),((2790188363:ℚ)/5000000000),((2956024511:ℚ)/5000000000),((13010565089:ℚ)/25750000000),((30292171577:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3731100991:ℚ)/5000000000),((-2144588887483178708111782215335393836217965747387453436732819:ℚ)/8090949606400000000000000000000000000000000000000000000000000),((-1424160814540344943884487061:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/8),((7:ℚ)/16),((5821418771:ℚ)/10000000000),((1538202679:ℚ)/2500000000),((26744256313:ℚ)/53400000000),((15567418753:ℚ)/25750000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1745594833:ℚ)/2500000000),((-166043709331555263983627237390280781376041389284593713682337:ℚ)/633947063012695312500000000000000000000000000000000000000000),((-354796635695381661062703781:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((6062203501:ℚ)/10000000000),((6273104359:ℚ)/10000000000),((27466610503:ℚ)/54350000000),((63111730513:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((6473937581:ℚ)/10000000000),((-88112856811695880812693204446096898808174624575528771126689833:ℚ)/333187806544400000000000000000000000000000000000000000000000000),((-5713003894227378830425905221:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((3091254017:ℚ)/5000000000),((1598335991:ℚ)/2500000000),((1987680293:ℚ)/3950000000),((15988351937:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3103359297:ℚ)/5000000000),((-3216135648869206630392896851737917032383922534478268547819:ℚ)/12231025854832458496093750000000000000000000000000000000000),((-356259440321516582979424421:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/8),((7:ℚ)/16),((315137907:ℚ)/500000000),((3256766167:ℚ)/5000000000),((1409413721:ℚ)/2812500000),((32397363169:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2964620431:ℚ)/5000000000),((-4164630391778082042366653210009489460550426889649696703:ℚ)/15925063403320312500000000000000000000000000000000000000),((-1421537367320635538238725349:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/8),((7:ℚ)/16),((1605739161:ℚ)/2500000000),((1658418021:ℚ)/2500000000),((648837953:ℚ)/1300000000),((5469642049:ℚ)/9375000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1127991469:ℚ)/2000000000),((-8385612759704497957348843116118838210677747082085691561:ℚ)/32234191894531250000000000000000000000000000000000000000),((-18654606518559756978736799:ℚ)/48640000000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((6543106179:ℚ)/10000000000),((1688441413:ℚ)/2500000000),((28909318537:ℚ)/58150000000),((16619089891:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((213476597:ℚ)/400000000),((-4653513846901752785791225706893664201212849515089292985343507:ℚ)/17978144262650000000000000000000000000000000000000000000000000),((-353419057205102600698025229:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((3331604601:ℚ)/5000000000),((6873815313:ℚ)/10000000000),((14634813803:ℚ)/29550000000),((67316707191:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5017586723:ℚ)/10000000000),((-73715568032628478910086414679455763959813192059839812830313399:ℚ)/286162602765576562500000000000000000000000000000000000000000000),((-5637264128587880123618472629:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((3:ℚ)/8),((7:ℚ)/16),((1695817001:ℚ)/2500000000),((111152989:ℚ)/156250000),((121433623:ℚ)/250000000),((1078070923:ℚ)/1846875000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2339301763:ℚ)/5000000000),((-367380454021897759375452910099945936518880327195607:ℚ)/1458239173889160156250000000000000000000000000000000),((-1355261630100036710663311:ℚ)/3610000000000000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((3:ℚ)/8),((7:ℚ)/16),((7023261387:ℚ)/10000000000),((14830667:ℚ)/19531250),((30349784161:ℚ)/64800000000),((141314669:ℚ)/238281250),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((980219153:ℚ)/2500000000),((-91601126046302376599085449260325788341715259013629080973:ℚ)/378728826141357421875000000000000000000000000000000000000),((-2619803991976374305705547:ℚ)/7220000000000000000000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/8),((7:ℚ)/16),((3751401623:ℚ)/5000000000),((9507013129:ℚ)/10000000000),((15894204869:ℚ)/40000000000),((85749091903:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1601024667:ℚ)/10000000000),((-101491397338405046162342741537409859674014608926961421407:ℚ)/503884800000000000000000000000000000000000000000000000000),((-182640928292004173:ℚ)/486400000000000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/8),((7:ℚ)/16),((4708305391:ℚ)/5000000000),((6661519281:ℚ)/5000000000),((18764916173:ℚ)/55200000000),((56230634967:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-213898747300097735530707193445139167926621351880077736309327:ℚ)/1269600000000000000000000000000000000000000000000000000000000),((-387187991:ℚ)/1024000000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC23
#check @N11Formalization.C450Source31GroupedC23.bound
#print axioms N11Formalization.C450Source31GroupedC23.valid0
#print axioms N11Formalization.C450Source31GroupedC23.valid1
#print axioms N11Formalization.C450Source31GroupedC23.valid2
#print axioms N11Formalization.C450Source31GroupedC23.valid3
#print axioms N11Formalization.C450Source31GroupedC23.valid4
#print axioms N11Formalization.C450Source31GroupedC23.valid5
#print axioms N11Formalization.C450Source31GroupedC23.valid6
#print axioms N11Formalization.C450Source31GroupedC23.valid7
#print axioms N11Formalization.C450Source31GroupedC23.valid8
#print axioms N11Formalization.C450Source31GroupedC23.valid9
#print axioms N11Formalization.C450Source31GroupedC23.valid10
#print axioms N11Formalization.C450Source31GroupedC23.valid11
#print axioms N11Formalization.C450Source31GroupedC23.bound
#print axioms N11Formalization.C450Source31GroupedC23.endpoint_checks
