import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((3008895879:ℚ)/5000000000),((653880057:ℚ)/1000000000),((1322965293:ℚ)/4450000000),((26460647:ℚ)/64000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6570218083:ℚ)/10000000000),((12579033294196842074652290361749:ℚ)/519110656000000000000000000000000),((-4907243036847971086874987:ℚ)/29573120000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((3247099111:ℚ)/5000000000),((1694214609:ℚ)/2500000000),((4207099111:ℚ)/13825000000),((2110214609:ℚ)/5340000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((682761569:ℚ)/1250000000),((18867317776603318997375872868871254504149475000991970969987:ℚ)/873122752930050000000000000000000000000000000000000000000000),((-31690451673970865360742203:ℚ)/184832000000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((1683082169:ℚ)/2500000000),((6895873189:ℚ)/10000000000),((2163082169:ℚ)/7031250000),((1222839027:ℚ)/3160000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4825107409:ℚ)/10000000000),((109138258166001890745646113595207045625744109037702481:ℚ)/5324821200000000000000000000000000000000000000000000000),((-515204686895823104339721123:ℚ)/2957312000000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((685137787:ℚ)/1000000000),((7014879119:ℚ)/10000000000),((877137787:ℚ)/2860000000),((8678879119:ℚ)/22500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2237899921:ℚ)/5000000000),((29561326145255597277013837729109636428618891153135396425751:ℚ)/1455793066406250000000000000000000000000000000000000000000000),((-519253200169150338049134843:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/4),((5:ℚ)/16),((697041709:ℚ)/1000000000),((221074341:ℚ)/312500000),((889041709:ℚ)/2883750000),((273074341:ℚ)/715000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2049506723:ℚ)/5000000000),((20081325042798895574313173951440429432701858065490976007:ℚ)/1013239438902539062500000000000000000000000000000000000000),((-511064612721794879440403:ℚ)/2888000000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((3514966557:ℚ)/5000000000),((356693833:ℚ)/500000000),((4474966557:ℚ)/14537500000),((439893833:ℚ)/1153500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((121807467:ℚ)/312500000),((3415507060607915626607598898350929287063630871165238619:ℚ)/172993975840834031250000000000000000000000000000000000000),((-1313383757888917271327307:ℚ)/7393280000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/4),((5:ℚ)/16),((7089446827:ℚ)/10000000000),((7193372413:ℚ)/10000000000),((9009446827:ℚ)/29312500000),((8857372413:ℚ)/23260000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((460787267:ℚ)/1250000000),((85084567256795499437853952763534404597911542159905909234077:ℚ)/4325086948348337500000000000000000000000000000000000000000000),((-527376514695982160852196147:ℚ)/2957312000000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((7148958283:ℚ)/10000000000),((7252866219:ℚ)/10000000000),((9068958283:ℚ)/29550000000),((8916866219:ℚ)/23450000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1731243607:ℚ)/5000000000),((686438206706614837633897386843699403884000325952455942099:ℚ)/35012850669726562500000000000000000000000000000000000000000),((-27863115784829718582631697:ℚ)/155648000000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/4),((5:ℚ)/16),((7208467539:ℚ)/10000000000),((11699773:ℚ)/16000000),((9128467539:ℚ)/29787500000),((4787391:ℚ)/12608000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((402980883:ℚ)/1250000000),((1390091730839705120653893871609288854619497520097271:ℚ)/71132275598945484800000000000000000000000000000000000),((-6802195977849804797823:ℚ)/37853593600000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((7267974647:ℚ)/10000000000),((7371848177:ℚ)/10000000000),((9187974647:ℚ)/30025000000),((9035848177:ℚ)/23830000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2966796439:ℚ)/10000000000),((148552839888657837998738954295737229972848641068906959520937:ℚ)/7624619518642455859375000000000000000000000000000000000000000),((-533443599063083065304556027:ℚ)/2957312000000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((3663739829:ℚ)/5000000000),((936352861:ℚ)/1250000000),((4623739829:ℚ)/15250000000),((1144352861:ℚ)/3002500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((671512393:ℚ)/2500000000),((12416345284415875524832209692366637954673946768407273029:ℚ)/629489855402441406250000000000000000000000000000000000000),((-8366156841332320809943923:ℚ)/46208000000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((3723241793:ℚ)/5000000000),((3864375947:ℚ)/5000000000),((4683241793:ℚ)/15725000000),((4696375947:ℚ)/12200000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((2013350461:ℚ)/10000000000),((1332811125242259736784912357206738535222246955260031287211:ℚ)/66031610162500000000000000000000000000000000000000000000000),((-22182617910323697:ℚ)/121600000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((7684468361:ℚ)/10000000000),((7966655677:ℚ)/10000000000),((9604468361:ℚ)/32400000000),((9630655677:ℚ)/25160000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((4353081506594154469296486823304108565064707616912484427151:ℚ)/217701143737200000000000000000000000000000000000000000000000),((-188634741:ℚ)/1024000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((3961212313:ℚ)/5000000000),((2467298541:ℚ)/2500000000),((4921212313:ℚ)/20000000000),((2883298541:ℚ)/6480000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((8176414388294398049859095690685128828952538069981783:ℚ)/318864600000000000000000000000000000000000000000000000),((-188634741:ℚ)/1024000000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((9825292859:ℚ)/10000000000),((2734434339:ℚ)/2000000000),((11745292859:ℚ)/55200000000),((3067234339:ℚ)/6400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((3496558993423826222509109469378864259:ℚ)/104005632000000000000000000000000000000),((-188634741:ℚ)/1024000000)⟩
theorem valid14 : Valid source14 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source14 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source14 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source14 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source14 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source14 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC21
#check @N11Formalization.C450Source14GroupedC21.bound
#print axioms N11Formalization.C450Source14GroupedC21.valid0
#print axioms N11Formalization.C450Source14GroupedC21.valid1
#print axioms N11Formalization.C450Source14GroupedC21.valid2
#print axioms N11Formalization.C450Source14GroupedC21.valid3
#print axioms N11Formalization.C450Source14GroupedC21.valid4
#print axioms N11Formalization.C450Source14GroupedC21.valid5
#print axioms N11Formalization.C450Source14GroupedC21.valid6
#print axioms N11Formalization.C450Source14GroupedC21.valid7
#print axioms N11Formalization.C450Source14GroupedC21.valid8
#print axioms N11Formalization.C450Source14GroupedC21.valid9
#print axioms N11Formalization.C450Source14GroupedC21.valid10
#print axioms N11Formalization.C450Source14GroupedC21.valid11
#print axioms N11Formalization.C450Source14GroupedC21.valid12
#print axioms N11Formalization.C450Source14GroupedC21.valid13
#print axioms N11Formalization.C450Source14GroupedC21.valid14
#print axioms N11Formalization.C450Source14GroupedC21.bound
#print axioms N11Formalization.C450Source14GroupedC21.endpoint_checks
