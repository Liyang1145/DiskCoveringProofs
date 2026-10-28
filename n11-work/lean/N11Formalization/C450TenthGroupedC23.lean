import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC23
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((3:ℚ)/8),((7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/8),((7:ℚ)/16),((6034043121:ℚ)/10000000000),((818550623:ℚ)/1250000000),((20662129363:ℚ)/53400000000),((6449854361:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3267563591:ℚ)/5000000000),((4301212844337924582690287:ℚ)/712890000000000000000000000),((-232874398076785969324393041:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((6509645657:ℚ)/10000000000),((6786131789:ℚ)/10000000000),((22088936971:ℚ)/55300000000),((53262922523:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5422836811:ℚ)/10000000000),((31470756477403542795278845382075036452542696513832587522394909:ℚ)/6984982023440400000000000000000000000000000000000000000000000000),((-237012596084122733468945249:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/8),((7:ℚ)/16),((6747415819:ℚ)/10000000000),((3452494719:ℚ)/5000000000),((22802247457:ℚ)/56250000000),((27047463033:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4782148137:ℚ)/10000000000),((6701527112895500596856465541773814824298255593204311957:ℚ)/1747206956250000000000000000000000000000000000000000000000),((-239094383477276078265581161:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/8),((7:ℚ)/16),((1716573511:ℚ)/2500000000),((3511921753:ℚ)/5000000000),((5789720533:ℚ)/14300000000),((27463452271:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((88604681:ℚ)/200000000),((85091045796744763695998981870171976525120718496505906321811:ℚ)/22746766662597656250000000000000000000000000000000000000000000),((-15008653523447952639911521:ℚ)/115520000000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/8),((7:ℚ)/16),((1746292001:ℚ)/2500000000),((7083269253:ℚ)/10000000000),((5878876003:ℚ)/14418750000),((55342884771:ℚ)/114400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((4050034113:ℚ)/10000000000),((4756780258077602361518514091451120362406174142290858568913111:ℚ)/1383409580581600000000000000000000000000000000000000000000000000),((-15074040693837907849260401:ℚ)/115520000000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((140892069:ℚ)/200000000),((7142694169:ℚ)/10000000000),((473876207:ℚ)/1163000000),((55758859183:ℚ)/115350000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((480840199:ℚ)/1250000000),((588299976047832997378002557748952242203753070072821610770321:ℚ)/172993975840834031250000000000000000000000000000000000000000000),((-96683417861629059241161:ℚ)/739328000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/8),((7:ℚ)/16),((7104037907:ℚ)/10000000000),((1800529569:ℚ)/2500000000),((23872113721:ℚ)/58625000000),((14043706983:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((908161319:ℚ)/2500000000),((28425017536789101407101682723090148814229778224656942768603:ℚ)/8447435445992846679687500000000000000000000000000000000000000),((-242232969259832112858524249:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((7163471399:ℚ)/10000000000),((7261541593:ℚ)/10000000000),((24050414197:ℚ)/59100000000),((56590791151:ℚ)/117250000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((340577181:ℚ)/1000000000),((418622080036727730689746420696039435751779561513169296809157:ℚ)/125671124725268554687500000000000000000000000000000000000000000),((-242757925103832329705173601:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/8),((7:ℚ)/16),((144458079:ℚ)/200000000),((3660482069:ℚ)/5000000000),((484574237:ℚ)/1191500000),((28503374483:ℚ)/59100000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3163344477:ℚ)/10000000000),((72512367138716880612562164511280824004248429096030348542899149:ℚ)/21979195875223481250000000000000000000000000000000000000000000000),((-97313364948837188782641:ℚ)/739328000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((7282335581:ℚ)/10000000000),((738038593:ℚ)/1000000000),((24407006743:ℚ)/60050000000),((5742270151:ℚ)/11915000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1450731157:ℚ)/5000000000),((3115623441330643197418948259557468875027170919896444272251:ℚ)/953077439830306982421875000000000000000000000000000000000000),((-243809431224939850216267961:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/8),((7:ℚ)/16),((1835441579:ℚ)/2500000000),((3749613663:ℚ)/5000000000),((6146324737:ℚ)/15250000000),((29127295641:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1307139967:ℚ)/5000000000),((284420407139507518724079527145240433123113282919392368241:ℚ)/82556046610156250000000000000000000000000000000000000000000),((-15270998865628458158625641:ℚ)/115520000000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((7460625177:ℚ)/10000000000),((309476073:ℚ)/400000000),((24941875531:ℚ)/62900000000),((2396732511:ℚ)/4880000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((959039107:ℚ)/5000000000),((271476133674422964215439084563195485929328240705806933251:ℚ)/71842391856800000000000000000000000000000000000000000000000),((-679752573465867126536889:ℚ)/5120000000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/8),((7:ℚ)/16),((7698333021:ℚ)/10000000000),((7974566081:ℚ)/10000000000),((25654999063:ℚ)/64800000000),((61581962567:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((300070834611219920543221179933088745839722875200013758187947:ℚ)/81637928901450000000000000000000000000000000000000000000000000),((-4269913:ℚ)/32000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/8),((7:ℚ)/16),((3968014331:ℚ)/5000000000),((4937799517:ℚ)/5000000000),((13184042993:ℚ)/40000000000),((37444596619:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((22671899548527079954133222673171151:ℚ)/3000000000000000000000000000000000000),((-4269913:ℚ)/32000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/8),((7:ℚ)/16),((9837258937:ℚ)/10000000000),((3419202807:ℚ)/2500000000),((32071776811:ℚ)/110400000000),((25374419649:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((36076650387901547373261983:ℚ)/3047040000000000000000000000),((-4269913:ℚ)/32000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound tenth nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC23
#check @N11Formalization.C450TenthGroupedC23.bound
#print axioms N11Formalization.C450TenthGroupedC23.valid0
#print axioms N11Formalization.C450TenthGroupedC23.valid1
#print axioms N11Formalization.C450TenthGroupedC23.valid2
#print axioms N11Formalization.C450TenthGroupedC23.valid3
#print axioms N11Formalization.C450TenthGroupedC23.valid4
#print axioms N11Formalization.C450TenthGroupedC23.valid5
#print axioms N11Formalization.C450TenthGroupedC23.valid6
#print axioms N11Formalization.C450TenthGroupedC23.valid7
#print axioms N11Formalization.C450TenthGroupedC23.valid8
#print axioms N11Formalization.C450TenthGroupedC23.valid9
#print axioms N11Formalization.C450TenthGroupedC23.valid10
#print axioms N11Formalization.C450TenthGroupedC23.valid11
#print axioms N11Formalization.C450TenthGroupedC23.valid12
#print axioms N11Formalization.C450TenthGroupedC23.valid13
#print axioms N11Formalization.C450TenthGroupedC23.valid14
#print axioms N11Formalization.C450TenthGroupedC23.bound
#print axioms N11Formalization.C450TenthGroupedC23.endpoint_checks
