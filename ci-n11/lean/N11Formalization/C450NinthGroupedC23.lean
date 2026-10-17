import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC23
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((3:ℚ)/8),((7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/8),((7:ℚ)/16),((3026659489:ℚ)/5000000000),((6564951277:ℚ)/10000000000),((10199978467:ℚ)/26700000000),((51074658939:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6493295959:ℚ)/10000000000),((1299150775120285085323571:ℚ)/178222500000000000000000000),((-51007578598840609571926831:ℚ)/462080000000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((3264397433:ℚ)/5000000000),((3401312433:ℚ)/5000000000),((10913192299:ℚ)/27650000000),((26369187031:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1343453987:ℚ)/2500000000),((5073615080369048075502579930590984028897941336643264278918299:ℚ)/873122752930050000000000000000000000000000000000000000000000000),((-51979362366076024933154879:ℚ)/462080000000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/8),((7:ℚ)/16),((6766508251:ℚ)/10000000000),((3460728629:ℚ)/5000000000),((22539524753:ℚ)/56250000000),((26785100403:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4727268261:ℚ)/10000000000),((63138420859630754059277178760293460247729283515291739403:ℚ)/12230448693750000000000000000000000000000000000000000000000),((-209883620496222058487503511:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((3:ℚ)/8),((7:ℚ)/16),((688535953:ℚ)/1000000000),((3490436209:ℚ)/5000000000),((2289607859:ℚ)/5672500000),((26993053463:ℚ)/56250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((174853911:ℚ)/400000000),((27818720673025567285249431922151594894029368475095469707519481:ℚ)/5726860304260253906250000000000000000000000000000000000000000000),((-2108723615656646658910799:ℚ)/18483200000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((3:ℚ)/8),((7:ℚ)/16),((868097987:ℚ)/1250000000),((7040286911:ℚ)/10000000000),((2884293961:ℚ)/7150000000),((54402008377:ℚ)/113450000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1045709741:ℚ)/2500000000),((2762762233996305165767253750801745944465375530527853877947:ℚ)/574225179201781250000000000000000000000000000000000000000000),((-3302627289130433809704359:ℚ)/28880000000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/8),((7:ℚ)/16),((7004207441:ℚ)/10000000000),((443731297:ℚ)/625000000),((23252622323:ℚ)/57675000000),((3426119079:ℚ)/7150000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((398597513:ℚ)/1000000000),((4830295727003927042517638213642073205548124417518191164619:ℚ)/1013239438902539062500000000000000000000000000000000000000000),((-211864874558994110018147791:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((3531815093:ℚ)/5000000000),((3579556979:ℚ)/5000000000),((11715445279:ℚ)/29075000000),((9205632951:ℚ)/19225000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((755889411:ℚ)/2000000000),((11353231409761151811156383167848710867574793115899022083793:ℚ)/2402694108900472656250000000000000000000000000000000000000000),((-53090636466568625586875639:ℚ)/462080000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/8),((7:ℚ)/16),((7123052149:ℚ)/10000000000),((1443705309:ℚ)/2000000000),((23609156447:ℚ)/58625000000),((11129937163:ℚ)/23260000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((222598117:ℚ)/625000000),((60793169643206636764987187118710184823471228180757449612303:ℚ)/12975260845045012500000000000000000000000000000000000000000000),((-212861160539005860306734711:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((7182473351:ℚ)/10000000000),((7277938527:ℚ)/10000000000),((23787420053:ℚ)/59100000000),((56065569689:ℚ)/117250000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((52033007:ℚ)/156250000),((4088344116013872994333631652709820057769233196430537441497967:ℚ)/879697873076879882812500000000000000000000000000000000000000000),((-213360718716401770334395711:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/8),((7:ℚ)/16),((7241893809:ℚ)/10000000000),((3668674959:ℚ)/5000000000),((23965681427:ℚ)/59575000000),((28240724713:ℚ)/59100000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1541006067:ℚ)/5000000000),((101357893804990841847230826938561318529182455960146260587260733:ℚ)/21979195875223481250000000000000000000000000000000000000000000000),((-213861220505294895238507791:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((3650656771:ℚ)/5000000000),((7396760733:ℚ)/10000000000),((12071970313:ℚ)/30025000000),((56897325131:ℚ)/119150000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((351607951:ℚ)/1250000000),((4362762443059396782482124585957545699983765529450988959802437:ℚ)/953077439830306982421875000000000000000000000000000000000000000),((-53590666507624856325925351:ℚ)/462080000000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/8),((7:ℚ)/16),((3680366283:ℚ)/5000000000),((7515580689:ℚ)/10000000000),((12161098849:ℚ)/30500000000),((57729064823:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((503183069:ℚ)/2000000000),((190643973375230764150495521070343032239005314593601226054489:ℚ)/40287350745756250000000000000000000000000000000000000000000000),((-53716263848163951229567479:ℚ)/462080000000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((1495913711:ℚ)/2000000000),((484575891:ℚ)/625000000),((133398409:ℚ)/340000000),((3712031237:ℚ)/7625000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((891298803:ℚ)/5000000000),((59168936606345564626499533564123194024808476056882867:ℚ)/11775747680664062500000000000000000000000000000000000000),((-8634906642779323095281231:ℚ)/73932800000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/8),((7:ℚ)/16),((1929308183:ℚ)/2500000000),((499427499:ℚ)/625000000),((6347924549:ℚ)/16200000000),((3815992493:ℚ)/7862500000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((97854786284101214683429130659119801180494650717936863331:ℚ)/19931134985705566406250000000000000000000000000000000000000),((-3004123:ℚ)/25600000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/8),((7:ℚ)/16),((7954887273:ℚ)/10000000000),((1978326137:ℚ)/2000000000),((26104661819:ℚ)/80000000000),((4957427653:ℚ)/8640000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((100923115825667928544095261634102427:ℚ)/12000000000000000000000000000000000000),((-3004123:ℚ)/25600000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/8),((7:ℚ)/16),((492792957:ℚ)/500000000),((13692558663:ℚ)/10000000000),((1590378871:ℚ)/5520000000),((100967910641:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((94913796215897530917899:ℚ)/7617600000000000000000000),((-3004123:ℚ)/25600000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound ninth nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC23
#check @N11Formalization.C450NinthGroupedC23.bound
#print axioms N11Formalization.C450NinthGroupedC23.valid0
#print axioms N11Formalization.C450NinthGroupedC23.valid1
#print axioms N11Formalization.C450NinthGroupedC23.valid2
#print axioms N11Formalization.C450NinthGroupedC23.valid3
#print axioms N11Formalization.C450NinthGroupedC23.valid4
#print axioms N11Formalization.C450NinthGroupedC23.valid5
#print axioms N11Formalization.C450NinthGroupedC23.valid6
#print axioms N11Formalization.C450NinthGroupedC23.valid7
#print axioms N11Formalization.C450NinthGroupedC23.valid8
#print axioms N11Formalization.C450NinthGroupedC23.valid9
#print axioms N11Formalization.C450NinthGroupedC23.valid10
#print axioms N11Formalization.C450NinthGroupedC23.valid11
#print axioms N11Formalization.C450NinthGroupedC23.valid12
#print axioms N11Formalization.C450NinthGroupedC23.valid13
#print axioms N11Formalization.C450NinthGroupedC23.valid14
#print axioms N11Formalization.C450NinthGroupedC23.valid15
#print axioms N11Formalization.C450NinthGroupedC23.bound
#print axioms N11Formalization.C450NinthGroupedC23.endpoint_checks
