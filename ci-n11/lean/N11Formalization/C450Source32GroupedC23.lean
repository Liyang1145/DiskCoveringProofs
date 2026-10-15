import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC23
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((3:ℚ)/8),((7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/8),((7:ℚ)/16),((5556410249:ℚ)/10000000000),((1472663759:ℚ)/2500000000),((26269230747:ℚ)/51500000000),((15268646313:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7508538111:ℚ)/10000000000),((-59133772764315687685115254879695130333446622459234611955029:ℚ)/202273740160000000000000000000000000000000000000000000000000),((-178736812928283325420971131:ℚ)/462080000000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/8),((7:ℚ)/16),((5797698141:ℚ)/10000000000),((6131650631:ℚ)/10000000000),((8997698141:ℚ)/17800000000),((62761554417:ℚ)/103000000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1406158001:ℚ)/2000000000),((-781505422029996225007141933853775726117309151402271547281949:ℚ)/2704840802187500000000000000000000000000000000000000000000000),((-2846774710743685037427823211:ℚ)/7393280000000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((6038710467:ℚ)/10000000000),((6252054841:ℚ)/10000000000),((27716131401:ℚ)/54350000000),((63604383887:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((6525019431:ℚ)/10000000000),((-174714684316141848462202981119751286692615952364673103402741897:ℚ)/599738051779920000000000000000000000000000000000000000000000000),((-2862727228834361276811156331:ℚ)/7393280000000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((3079561293:ℚ)/5000000000),((796550133:ℚ)/1250000000),((14038683879:ℚ)/27650000000),((8055850931:ℚ)/13587500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((625943249:ℚ)/1000000000),((-13021333896613122271001699035178803695428471646297923613229:ℚ)/44949020016509284973144531250000000000000000000000000000000),((-133814873665587798161305417:ℚ)/346560000000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/8),((7:ℚ)/16),((3139738217:ℚ)/5000000000),((1623173079:ℚ)/2500000000),((1579912739:ℚ)/3125000000),((16322211553:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((373990111:ℚ)/625000000),((-12746394397406757158163812432530516305381235314289649:ℚ)/44236287231445312500000000000000000000000000000000000),((-533646197973898476841987873:ℚ)/1386240000000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/8),((7:ℚ)/16),((6399775043:ℚ)/10000000000),((1322586281:ℚ)/2000000000),((28799325129:ℚ)/57200000000),((13226103967:ℚ)/22500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5696762009:ℚ)/10000000000),((-83466910524126885902952613824427248541016353927826320315331:ℚ)/291158613281250000000000000000000000000000000000000000000000),((-113476604878048924247776011:ℚ)/295731200000000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((1630005309:ℚ)/2500000000),((6733120951:ℚ)/10000000000),((7290015927:ℚ)/14537500000),((66971846657:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((539632573:ℚ)/1000000000),((-65646987452922132529981280847175380467824404977556991407214719:ℚ)/230120246561920000000000000000000000000000000000000000000000000),((-2827124098907822643111861451:ℚ)/7393280000000000000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((3320108823:ℚ)/5000000000),((34266317:ℚ)/50000000),((4920108823:ℚ)/9850000000),((339064219:ℚ)/581500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1016025771:ℚ)/2000000000),((-677115753937477580635209822247070265213153170095148343:ℚ)/2384688356379804687500000000000000000000000000000000000),((-70418513564577332521939:ℚ)/184832000000000000000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((3:ℚ)/8),((7:ℚ)/16),((6760366729:ℚ)/10000000000),((3546708003:ℚ)/5000000000),((29881100187:ℚ)/61000000000),((34746956021:ℚ)/59100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4744985593:ℚ)/10000000000),((-801232156827079394576148635913970082151466111027213636098619:ℚ)/2880403834466250000000000000000000000000000000000000000000000),((-2078186023061143900680764377:ℚ)/5544960000000000000000000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((3:ℚ)/8),((7:ℚ)/16),((1750132991:ℚ)/2500000000),((302929899:ℚ)/400000000),((2550132991:ℚ)/5400000000),((2914109293:ℚ)/4880000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((499802127:ℚ)/1250000000),((-9458053741846417418717725680993880159046993224409065003:ℚ)/35300085120000000000000000000000000000000000000000000000),((-12826772864181243269431753:ℚ)/35487744000000000000000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/8),((7:ℚ)/16),((7480386401:ℚ)/10000000000),((9487932383:ℚ)/10000000000),((32041159203:ℚ)/80000000000),((9583947409:ℚ)/14400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((177651849:ℚ)/1000000000),((-2540005726536454816008776831202396326665087918613740391:ℚ)/11197440000000000000000000000000000000000000000000000000),((-181374434366143439:ℚ)/486400000000000000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/8),((7:ℚ)/16),((9395140877:ℚ)/10000000000),((13305089969:ℚ)/10000000000),((12595140877:ℚ)/36800000000),((112975629783:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-131578395620681110899771184327486111975190686195326376148259:ℚ)/677120000000000000000000000000000000000000000000000000000000),((-192526281:ℚ)/512000000)⟩
theorem valid11 : Valid source32 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC23
#check @N11Formalization.C450Source32GroupedC23.bound
#print axioms N11Formalization.C450Source32GroupedC23.valid0
#print axioms N11Formalization.C450Source32GroupedC23.valid1
#print axioms N11Formalization.C450Source32GroupedC23.valid2
#print axioms N11Formalization.C450Source32GroupedC23.valid3
#print axioms N11Formalization.C450Source32GroupedC23.valid4
#print axioms N11Formalization.C450Source32GroupedC23.valid5
#print axioms N11Formalization.C450Source32GroupedC23.valid6
#print axioms N11Formalization.C450Source32GroupedC23.valid7
#print axioms N11Formalization.C450Source32GroupedC23.valid8
#print axioms N11Formalization.C450Source32GroupedC23.valid9
#print axioms N11Formalization.C450Source32GroupedC23.valid10
#print axioms N11Formalization.C450Source32GroupedC23.valid11
#print axioms N11Formalization.C450Source32GroupedC23.bound
#print axioms N11Formalization.C450Source32GroupedC23.endpoint_checks
