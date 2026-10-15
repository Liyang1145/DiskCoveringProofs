import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((5:ℚ)/16),((3:ℚ)/8),((1112092253:ℚ)/2000000000),((2950851619:ℚ)/5000000000),((1956892253:ℚ)/4120000000),((14292554857:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3750361093:ℚ)/5000000000),((-3354222831715736769001872382858811540719340141676415161391:ℚ)/9819113600000000000000000000000000000000000000000000000000),((-10642654588788081926664043:ℚ)/28880000000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((2901418311:ℚ)/5000000000),((6143671237:ℚ)/10000000000),((1671139437:ℚ)/3560000000),((29311013711:ℚ)/51500000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((3510163287:ℚ)/5000000000),((-6398045062347191881244930942330724212878855551137852782791:ℚ)/18994668554687500000000000000000000000000000000000000000000),((-42453866746513034044336747:ℚ)/115520000000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((1511213767:ℚ)/2500000000),((3132267461:ℚ)/5000000000),((2567213767:ℚ)/5435000000),((14836802383:ℚ)/26700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1302338413:ℚ)/2000000000),((-4867953454101097284244454802468221667640487264351495146609:ℚ)/14368149431250000000000000000000000000000000000000000000000),((-10698240903595980921415723:ℚ)/28880000000000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((6165742583:ℚ)/10000000000),((6385324103:ℚ)/10000000000),((10389742583:ℚ)/22120000000),((30035972309:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((780568661:ℚ)/1250000000),((-2918045520371726643741251203623470874557096645152758633397:ℚ)/8670094276843261718750000000000000000000000000000000000000),((-42710737843832927834372467:ℚ)/115520000000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/16),((3:ℚ)/8),((6286554731:ℚ)/10000000000),((3253021341:ℚ)/5000000000),((10510554731:ℚ)/22500000000),((15199064023:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1193457601:ℚ)/2000000000),((-1553420437772961153976356242719656644276172155441334607:ℚ)/4644810159301757812500000000000000000000000000000000000),((-10654781535496172413270603:ℚ)/28880000000000000000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((6407295463:ℚ)/10000000000),((1656673573:ℚ)/2500000000),((10631295463:ℚ)/22880000000),((7690020719:ℚ)/14062500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2839194637:ℚ)/5000000000),((-91803951541695169821644733861922337637617327703866414857:ℚ)/276160240173339843750000000000000000000000000000000000000),((-2657383932430310396101327:ℚ)/7220000000000000000000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((3263984227:ℚ)/5000000000),((3373641159:ℚ)/5000000000),((5375984227:ℚ)/11630000000),((1414629407:ℚ)/2600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((537593983:ℚ)/1000000000),((-42226184301869896670457852432539655760794803001924477989:ℚ)/127755550000000000000000000000000000000000000000000000000),((-557997389272347098147137:ℚ)/1520000000000000000000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((664857713:ℚ)/1000000000),((10730953:ℚ)/15625000),((1087257713:ℚ)/2364000000),((49192859:ℚ)/90859375),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5057470949:ℚ)/10000000000),((-910751005058225523158880456161997017692217391489389:ℚ)/2770618523588776588439941406250000000000000000000000),((-695528201276649082529:ℚ)/1900000000000000000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((6769124687:ℚ)/10000000000),((7108695469:ℚ)/10000000000),((10993124687:ℚ)/24400000000),((32206086407:ℚ)/59100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2359850791:ℚ)/5000000000),((-1134090517076673972995755622337078209230169315313535067322143:ℚ)/3523562251600000000000000000000000000000000000000000000000000),((-41610740625401394345788443:ℚ)/115520000000000000000000000)⟩
theorem valid8 : Valid source35 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source35 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((3505024101:ℚ)/5000000000),((379492971:ℚ)/500000000),((624113789:ℚ)/1440000000),((1682478913:ℚ)/3050000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((198306377:ℚ)/500000000),((-796120848242454631338570303022177087334751738993587903:ℚ)/2571955200000000000000000000000000000000000000000000000),((-100364797574784678678883:ℚ)/288800000000000000000000)⟩
theorem valid9 : Valid source35 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((1498256229:ℚ)/2000000000),((594286023:ℚ)/625000000),((2343056229:ℚ)/6400000000),((2462858069:ℚ)/4050000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((846739313:ℚ)/5000000000),((-315472864066147621534551299775706764980760233439197337509:ℚ)/1194393600000000000000000000000000000000000000000000000000),((-36993888790187:ℚ)/102400000000000)⟩
theorem valid10 : Valid source35 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((9410206649:ℚ)/10000000000),((13330416587:ℚ)/10000000000),((13634206649:ℚ)/44160000000),((50871249761:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-10155349071839955064322175566928218220816148387975303547:ℚ)/44852428800000000000000000000000000000000000000000000000),((-11663071:ℚ)/32000000)⟩
theorem valid11 : Valid source35 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source35 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC22
#check @N11Formalization.C450Source35GroupedC22.bound
#print axioms N11Formalization.C450Source35GroupedC22.valid0
#print axioms N11Formalization.C450Source35GroupedC22.valid1
#print axioms N11Formalization.C450Source35GroupedC22.valid2
#print axioms N11Formalization.C450Source35GroupedC22.valid3
#print axioms N11Formalization.C450Source35GroupedC22.valid4
#print axioms N11Formalization.C450Source35GroupedC22.valid5
#print axioms N11Formalization.C450Source35GroupedC22.valid6
#print axioms N11Formalization.C450Source35GroupedC22.valid7
#print axioms N11Formalization.C450Source35GroupedC22.valid8
#print axioms N11Formalization.C450Source35GroupedC22.valid9
#print axioms N11Formalization.C450Source35GroupedC22.valid10
#print axioms N11Formalization.C450Source35GroupedC22.valid11
#print axioms N11Formalization.C450Source35GroupedC22.bound
#print axioms N11Formalization.C450Source35GroupedC22.endpoint_checks
