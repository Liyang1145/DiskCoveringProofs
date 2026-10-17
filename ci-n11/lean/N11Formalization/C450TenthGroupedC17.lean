import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((770885057:ℚ)/1250000000),((3333662589:ℚ)/5000000000),((64:ℚ)/1335),((6213662589:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6241537723:ℚ)/10000000000),((42590854592195841386093286650186715666707:ℚ)/2174741093376000000000000000000000000000000),((-5050099614694337:ℚ)/121600000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((6642823039:ℚ)/10000000000),((6786209479:ℚ)/10000000000),((256:ℚ)/5435),((12546209479:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2536538497:ℚ)/5000000000),((509205912090120291731941550469097421214300324895441853552083673:ℚ)/26988212330096400000000000000000000000000000000000000000000000000),((-43517406084233599:ℚ)/972800000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((270469697:ℚ)/400000000),((3452544579:ℚ)/5000000000),((128:ℚ)/2765),((6332544579:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4741022243:ℚ)/10000000000),((359696211451995269684316581259531714116498773306349285080799:ℚ)/19178248540377294921875000000000000000000000000000000000000000),((-1771858074304577:ℚ)/38912000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((6880655979:ℚ)/10000000000),((140479289:ℚ)/200000000),((256:ℚ)/5625),((255679289:ℚ)/2212000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((175437759:ℚ)/400000000),((2085736579539160244841428799985108810566102118084309:ℚ)/111821245200000000000000000000000000000000000000000000),((-45075459425324139:ℚ)/972800000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),(0:ℚ),((1:ℚ)/16),((6999563997:ℚ)/10000000000),((177085013:ℚ)/250000000),((512:ℚ)/11345),((321085013:ℚ)/2812500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((10004219:ℚ)/25000000),((13269264765432992189548780109331093289777635786720389825633:ℚ)/715857538032531738281250000000000000000000000000000000000000),((-45854430726470877:ℚ)/972800000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((7059016017:ℚ)/10000000000),((3571417787:ℚ)/5000000000),((32:ℚ)/715),((6451417787:ℚ)/56725000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1897932971:ℚ)/5000000000),((17255676634574226127949427558154097548941931754611301487543:ℚ)/933115916202894531250000000000000000000000000000000000000000),((-46243903347023697:ℚ)/972800000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),(0:ℚ),((1:ℚ)/16),((1779616689:ℚ)/2500000000),((7202269637:ℚ)/10000000000),((512:ℚ)/11535),((12962269637:ℚ)/114400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((894708413:ℚ)/2500000000),((76575373744740212094024258571611008765929552602811514725483459:ℚ)/4150228741744800000000000000000000000000000000000000000000000000),((-11658341893923249:ℚ)/243200000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((1435583249:ℚ)/2000000000),((3630851367:ℚ)/5000000000),((256:ℚ)/5815),((2170283789:ℚ)/19225000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((418550901:ℚ)/1250000000),((44236405008451759665076316028201631521690418607644615290081:ℚ)/2402694108900472656250000000000000000000000000000000000000000),((-9404564723112209:ℚ)/194560000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),(0:ℚ),((1:ℚ)/16),((1447472903:ℚ)/2000000000),((915141861:ℚ)/1250000000),((512:ℚ)/11725),((1635141861:ℚ)/14537500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1550799079:ℚ)/5000000000),((19400953193305064523824124306974758021766159336684138922089:ℚ)/1055929430749105834960937500000000000000000000000000000000000),((-9482454333942023:ℚ)/194560000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((1459362319:ℚ)/2000000000),((3690283061:ℚ)/5000000000),((128:ℚ)/2955),((6570283061:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2834124711:ℚ)/10000000000),((288059465010414367331239824398765583008373437705947691464367:ℚ)/15708890590658569335937500000000000000000000000000000000000000),((-9560342385624079:ℚ)/194560000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((1471251503:ℚ)/2000000000),((3749712959:ℚ)/5000000000),((256:ℚ)/6005),((6629712959:ℚ)/59100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1269730089:ℚ)/5000000000),((102293877022015664500939219160947676540493222656042434266965497:ℚ)/5582769915665081250000000000000000000000000000000000000000000000),((-9638228917464623:ℚ)/194560000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((3737572991:ℚ)/5000000000),((7618282289:ℚ)/10000000000),((64:ℚ)/1525),((13378282289:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((453780497:ℚ)/2500000000),((12059331061417162745937809876538065990329219144309826769849:ℚ)/660448372881250000000000000000000000000000000000000000000000),((-24484993904533631:ℚ)/486400000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((7594030129:ℚ)/10000000000),((8093676547:ℚ)/10000000000),((16:ℚ)/405),((13853676547:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((396386733:ℚ)/10000000000),((340869520177105481733503520834863456243538270099772494207143:ℚ)/18615279262500000000000000000000000000000000000000000000000000),((-49748802730314289:ℚ)/972800000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((2017381831:ℚ)/2500000000),((9994878691:ℚ)/10000000000),((4:ℚ)/125),((15754878691:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((47136591859989827827970480044255580849267463026153995997:ℚ)/2550916800000000000000000000000000000000000000000000000000),((-6551041:ℚ)/128000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((4985521613:ℚ)/5000000000),((13796289359:ℚ)/10000000000),((8:ℚ)/345),((19556289359:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((99696559361162662143242342002092787247513:ℚ)/4875264000000000000000000000000000000000000),((-6551041:ℚ)/128000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((2307:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC17
#check @N11Formalization.C450TenthGroupedC17.bound
#print axioms N11Formalization.C450TenthGroupedC17.valid0
#print axioms N11Formalization.C450TenthGroupedC17.valid1
#print axioms N11Formalization.C450TenthGroupedC17.valid2
#print axioms N11Formalization.C450TenthGroupedC17.valid3
#print axioms N11Formalization.C450TenthGroupedC17.valid4
#print axioms N11Formalization.C450TenthGroupedC17.valid5
#print axioms N11Formalization.C450TenthGroupedC17.valid6
#print axioms N11Formalization.C450TenthGroupedC17.valid7
#print axioms N11Formalization.C450TenthGroupedC17.valid8
#print axioms N11Formalization.C450TenthGroupedC17.valid9
#print axioms N11Formalization.C450TenthGroupedC17.valid10
#print axioms N11Formalization.C450TenthGroupedC17.valid11
#print axioms N11Formalization.C450TenthGroupedC17.valid12
#print axioms N11Formalization.C450TenthGroupedC17.valid13
#print axioms N11Formalization.C450TenthGroupedC17.valid14
#print axioms N11Formalization.C450TenthGroupedC17.bound
#print axioms N11Formalization.C450TenthGroupedC17.endpoint_checks
