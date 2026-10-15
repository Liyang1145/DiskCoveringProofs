import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((354261989:ℚ)/625000000),((6212012077:ℚ)/10000000000),((5165405857:ℚ)/6675000000),((48284084539:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3645196549:ℚ)/5000000000),((-240525516924701192012707985952223949:ℚ)/3717609960937500000000000000000000000),((-232405281140658954733858689:ℚ)/778240000000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((3071838389:ℚ)/5000000000),((3224893419:ℚ)/5000000000),((44413899057:ℚ)/55300000000),((8324751311:ℚ)/8900000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6294039521:ℚ)/10000000000),((-979098782108254845843643603058892548051609583307396239:ℚ)/13211904453125000000000000000000000000000000000000000000),((-172819791081525229631001203:ℚ)/583680000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((6381394227:ℚ)/10000000000),((6687543317:ℚ)/10000000000),((91918124951:ℚ)/114400000000),((51612803219:ℚ)/55300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5741447043:ℚ)/10000000000),((-668008972029225529911988859812687088105885268859456549:ℚ)/8997560000000000000000000000000000000000000000000000000),((-228445134381705844467773649:ℚ)/778240000000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((6619097211:ℚ)/10000000000),((6806415261:ℚ)/10000000000),((95008263743:ℚ)/116300000000),((52444906827:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((205478729:ℚ)/400000000),((-7234767540858678633111678778124234991038436651439917203:ℚ)/92170180488281250000000000000000000000000000000000000000),((-682360853292475645330386083:ℚ)/2334720000000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6737943723:ℚ)/10000000000),((86566041:ℚ)/125000000),((96553268399:ℚ)/118200000000),((665962287:ℚ)/726875000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2404580201:ℚ)/5000000000),((-7592231361603722963886762602127582439394238577494306899:ℚ)/96761752031250000000000000000000000000000000000000000000),((-106153830841421458991963:ℚ)/364800000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((6856787129:ℚ)/10000000000),((55877727:ℚ)/80000000),((98098232677:ℚ)/119150000000),((143181363:ℚ)/157600000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((445932589:ℚ)/1000000000),((-31913525428189591720295455213812363373420309373790492337:ℚ)/396454567001953125000000000000000000000000000000000000000),((-2283438074212005173993:ℚ)/7864320000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((6916207713:ℚ)/10000000000),((3522073779:ℚ)/5000000000),((98870700269:ℚ)/120100000000),((27054516453:ℚ)/29787500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1068615853:ℚ)/2500000000),((-680595802133883845433011706664015384293354507217365907:ℚ)/8458611333007812500000000000000000000000000000000000000),((-169101597749521012510744643:ℚ)/583680000000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((279025103:ℚ)/400000000),((142071567:ℚ)/200000000),((3985726339:ℚ)/4842000000),((1090500969:ℚ)/1201000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((408177579:ℚ)/1000000000),((-79254839854384280861927850422979362304705681587573:ℚ)/985421143125000000000000000000000000000000000000000),((-269966662011792699099947:ℚ)/933888000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((7035046733:ℚ)/10000000000),((447688017:ℚ)/625000000),((100415607529:ℚ)/122000000000),((1144605373:ℚ)/1260937500),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((970023409:ℚ)/2500000000),((-11404911405752241342353140385153435011197928746984956767:ℚ)/141863125000000000000000000000000000000000000000000000000),((-2630572147931310338346347:ℚ)/9120000000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((3547232601:ℚ)/5000000000),((1444487469:ℚ)/2000000000),((50594023813:ℚ)/61475000000),((11071412283:ℚ)/12200000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((29343437:ℚ)/80000000),((-364645750849523398730647015755821324627788786736759011:ℚ)/4537594170837402343750000000000000000000000000000000000),((-26877433400590097522998403:ℚ)/93388800000000000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((3576941499:ℚ)/5000000000),((3640932793:ℚ)/5000000000),((50980239487:ℚ)/61950000000),((27886529551:ℚ)/30737500000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((3443342621:ℚ)/10000000000),((-165784753891430872310285653807798666621655011501539241:ℚ)/2063818271484375000000000000000000000000000000000000000),((-55870395838005992267110409:ℚ)/194560000000000000000000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((3606650069:ℚ)/5000000000),((3700359827:ℚ)/5000000000),((51366450897:ℚ)/62900000000),((28302518789:ℚ)/30975000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((64074333:ℚ)/200000000),((-87512617351905359369794830257540001097685389477263:ℚ)/1116845474243164062500000000000000000000000000000000),((-55621768987477883830514689:ℚ)/194560000000000000000000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((3666066253:ℚ)/5000000000),((61107349:ℚ)/80000000),((52138861289:ℚ)/64800000000),((466151443:ℚ)/503200000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2662883203:ℚ)/10000000000),((-58787891891228467162527182821649154750681581500220749:ℚ)/787320000000000000000000000000000000000000000000000000),((-290550257:ℚ)/1024000000)⟩
theorem valid12 : Valid source16 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source16 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((7569789989:ℚ)/10000000000),((1192458729:ℚ)/1250000000),((107367269857:ℚ)/160000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((445961753:ℚ)/5000000000),((-2321778793555542681984188765616865563874596341800283173:ℚ)/60000000000000000000000000000000000000000000000000000000),((-290550257:ℚ)/1024000000)⟩
theorem valid13 : Valid source16 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((9470780357:ℚ)/10000000000),((13341138049:ℚ)/10000000000),((132080144641:ℚ)/220800000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-620842310454331482648959418684645341:ℚ)/33639321600000000000000000000000000000),((-290550257:ℚ)/1024000000)⟩
theorem valid14 : Valid source16 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source16 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source16 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC30
#check @N11Formalization.C450Source16GroupedC30.bound
#print axioms N11Formalization.C450Source16GroupedC30.valid0
#print axioms N11Formalization.C450Source16GroupedC30.valid1
#print axioms N11Formalization.C450Source16GroupedC30.valid2
#print axioms N11Formalization.C450Source16GroupedC30.valid3
#print axioms N11Formalization.C450Source16GroupedC30.valid4
#print axioms N11Formalization.C450Source16GroupedC30.valid5
#print axioms N11Formalization.C450Source16GroupedC30.valid6
#print axioms N11Formalization.C450Source16GroupedC30.valid7
#print axioms N11Formalization.C450Source16GroupedC30.valid8
#print axioms N11Formalization.C450Source16GroupedC30.valid9
#print axioms N11Formalization.C450Source16GroupedC30.valid10
#print axioms N11Formalization.C450Source16GroupedC30.valid11
#print axioms N11Formalization.C450Source16GroupedC30.valid12
#print axioms N11Formalization.C450Source16GroupedC30.valid13
#print axioms N11Formalization.C450Source16GroupedC30.valid14
#print axioms N11Formalization.C450Source16GroupedC30.bound
#print axioms N11Formalization.C450Source16GroupedC30.endpoint_checks
