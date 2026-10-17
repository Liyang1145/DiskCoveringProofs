import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((6287891399:ℚ)/10000000000),((3280708613:ℚ)/5000000000),((-2640708613:ℚ)/9920000000),((-4527891399:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5964157457:ℚ)/10000000000),((7319481264812062181338110518517792247734772775351621687:ℚ)/206753765869140625000000000000000000000000000000000000000),((7370121252201895965254161:ℚ)/147865600000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((6525838951:ℚ)/10000000000),((6799401477:ℚ)/10000000000),((-5519401477:ℚ)/20600000000),((-4765838951:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5381409177:ℚ)/10000000000),((249299488500454371024569787582507143228324068987044957:ℚ)/7090996777343750000000000000000000000000000000000000000),((85062487190432381554890803:ℚ)/1774387200000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((676375457:ℚ)/1000000000),((1729595217:ℚ)/2500000000),((-1409595217:ℚ)/5340000000),((-500375457:ℚ)/2717500000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4735219777:ℚ)/10000000000),((72168618093287709802378055245046503427595834632490653:ℚ)/2093051692510986328125000000000000000000000000000000000),((5101679614925320669523723:ℚ)/110899200000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((1376540291:ℚ)/2000000000),((3488933787:ℚ)/5000000000),((-2848933787:ℚ)/10870000000),((-1024540291:ℚ)/5482500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((68431281:ℚ)/156250000),((22135536287627945504241957778602136262637469029273753:ℚ)/647890697505187988281250000000000000000000000000000000),((19977404497081048605645683:ℚ)/443596800000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((6942172333:ℚ)/10000000000),((1759338089:ℚ)/2500000000),((-479779363:ℚ)/1827500000),((-5182172333:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4191290623:ℚ)/10000000000),((3218901392772221931643740379474821964453974211220895209:ℚ)/94315450734710693359375000000000000000000000000000000000),((1647219633078689147029449:ℚ)/36966400000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((7001641559:ℚ)/10000000000),((7096835263:ℚ)/10000000000),((-5816835263:ℚ)/22120000000),((-5241641559:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1997332391:ℚ)/5000000000),((9983282969255391920577434586396900394110865008864161129:ℚ)/292815413104200363159179687500000000000000000000000000000),((26074583755099344965096761:ℚ)/591462400000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((7061109177:ℚ)/10000000000),((3578158171:ℚ)/5000000000),((-2938158171:ℚ)/11155000000),((-5301109177:ℚ)/28125000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((29597079:ℚ)/78125000),((859859814686796382111189377726914271130925045180889523:ℚ)/25245035067200660705566406250000000000000000000000000000),((6448436997874644656616529:ℚ)/147865600000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((1780143807:ℚ)/2500000000),((7215795641:ℚ)/10000000000),((-659532849:ℚ)/2500000000),((-1340143807:ℚ)/7090625000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((11159079:ℚ)/31250000),((11846624742347563600612618896487188920439856431681:ℚ)/348139736324548721313476562500000000000000000000000),((25513006638139542439571689:ℚ)/591462400000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((28720159:ℚ)/40000000),((3637636601:ℚ)/5000000000),((-2997636601:ℚ)/11345000000),((-21680159:ℚ)/114400000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3339894279:ℚ)/10000000000),((45114866712267799178337883272321797713875490712813:ℚ)/1327005136600000000000000000000000000000000000000000),((6308089877151474629649769:ℚ)/147865600000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((7239502781:ℚ)/10000000000),((733474907:ℚ)/1000000000),((-605474907:ℚ)/2288000000),((-1826500927:ℚ)/9612500000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1546183309:ℚ)/5000000000),((65831615729060197299331428829344663252822579032733:ℚ)/1938050838917493820190429687500000000000000000000000),((249518064172687982412881:ℚ)/5914624000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((182474109:ℚ)/250000000),((3697111643:ℚ)/5000000000),((-3057111643:ℚ)/11535000000),((-138474109:ℚ)/726875000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2823977401:ℚ)/10000000000),((11746115200037415669512527941458970572510691934218481:ℚ)/346088226540470123291015625000000000000000000000000000),((6167836793284350548928081:ℚ)/147865600000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((7358424521:ℚ)/10000000000),((7513166921:ℚ)/10000000000),((-6233166921:ℚ)/23260000000),((-1866141507:ℚ)/9850000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2528085587:ℚ)/10000000000),((3703625640983644830893776583602867595187946191740967327:ℚ)/108539658190917968750000000000000000000000000000000000000),((24401931852230005638411529:ℚ)/591462400000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((934667591:ℚ)/1250000000),((7751036057:ℚ)/10000000000),((-2157012019:ℚ)/7880000000),((-714667591:ℚ)/3812500000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1799054141:ℚ)/10000000000),((2409732311395387703978042114853346601293512954367561:ℚ)/69907855987548828125000000000000000000000000000000000),((4900419099400797:ℚ)/121600000000000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((385757879:ℚ)/500000000),((32906837:ℚ)/40000000),((-27786837:ℚ)/97600000),((-297757879:ℚ)/1620000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((131715186789753098954605790565200385798016384197431:ℚ)/3752071875000000000000000000000000000000000000000000),((40226571:ℚ)/1024000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((102384193:ℚ)/125000000),((10128761497:ℚ)/10000000000),((-8848761497:ℚ)/25920000000),((-80384193:ℚ)/500000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((152807121406429550253768699820268301001637427126431:ℚ)/3955078125000000000000000000000000000000000000000000),((40226571:ℚ)/1024000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((10092497183:ℚ)/10000000000),((13931169067:ℚ)/10000000000),((-12651169067:ℚ)/32000000000),((-2777499061:ℚ)/18400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((26430780155086706977573240654193121239264484641208523:ℚ)/608350000000000000000000000000000000000000000000000000),((40226571:ℚ)/1024000000)⟩
theorem valid15 : Valid source12 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source12 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source12 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC12
#check @N11Formalization.C450Source12GroupedC12.bound
#print axioms N11Formalization.C450Source12GroupedC12.valid0
#print axioms N11Formalization.C450Source12GroupedC12.valid1
#print axioms N11Formalization.C450Source12GroupedC12.valid2
#print axioms N11Formalization.C450Source12GroupedC12.valid3
#print axioms N11Formalization.C450Source12GroupedC12.valid4
#print axioms N11Formalization.C450Source12GroupedC12.valid5
#print axioms N11Formalization.C450Source12GroupedC12.valid6
#print axioms N11Formalization.C450Source12GroupedC12.valid7
#print axioms N11Formalization.C450Source12GroupedC12.valid8
#print axioms N11Formalization.C450Source12GroupedC12.valid9
#print axioms N11Formalization.C450Source12GroupedC12.valid10
#print axioms N11Formalization.C450Source12GroupedC12.valid11
#print axioms N11Formalization.C450Source12GroupedC12.valid12
#print axioms N11Formalization.C450Source12GroupedC12.valid13
#print axioms N11Formalization.C450Source12GroupedC12.valid14
#print axioms N11Formalization.C450Source12GroupedC12.valid15
#print axioms N11Formalization.C450Source12GroupedC12.bound
#print axioms N11Formalization.C450Source12GroupedC12.endpoint_checks
