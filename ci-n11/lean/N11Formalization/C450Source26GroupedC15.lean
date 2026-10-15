import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/8),((-1:ℚ)/16),((1236328521:ℚ)/2000000000),((6486647963:ℚ)/10000000000),((1193352037:ℚ)/51500000000),((1963671479:ℚ)/19840000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((62086763:ℚ)/100000000),((3412365672928521094545848561478631158323:ℚ)/20712830992384000000000000000000000000000),((-8522603934754977103379039:ℚ)/35487744000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((6422162921:ℚ)/10000000000),((672669547:ℚ)/1000000000),((95330453:ℚ)/5340000000),((9577837079:ℚ)/103000000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5641910721:ℚ)/10000000000),((309710719582936401704330162060017116023236483470895089587321:ℚ)/1901841189038085937500000000000000000000000000000000000000000),((-74902342774817042119039413:ℚ)/295731200000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((3331232243:ℚ)/5000000000),((6846651403:ℚ)/10000000000),((833348597:ℚ)/54350000000),((1556255919:ℚ)/17800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((627452959:ℚ)/1250000000),((6680012620551956496888789621462520476846936667908733394591929:ℚ)/41648475818050000000000000000000000000000000000000000000000000),((-19697014017557806474736557:ℚ)/73932800000000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((6782540571:ℚ)/10000000000),((6966565291:ℚ)/10000000000),((713434709:ℚ)/55300000000),((9217459429:ℚ)/108700000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4680725467:ℚ)/10000000000),((73545099786870167429525653360193841223961032987127121758257753:ℚ)/460277964969055078125000000000000000000000000000000000000000000),((-242198776437114719911828439:ℚ)/887193600000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((1380514071:ℚ)/2000000000),((3543219653:ℚ)/5000000000),((296780347:ℚ)/28125000000),((1819485929:ℚ)/22120000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1079386309:ℚ)/2500000000),((124652451307792991464480607756194217364498918972910878497:ℚ)/782748716400000000000000000000000000000000000000000000000),((-9921502788943306086001439:ℚ)/35487744000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((3511278117:ℚ)/5000000000),((720627547:ℚ)/1000000000),((47372453:ℚ)/5720000000),((4488721883:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((980826007:ℚ)/2500000000),((3611774726637792967694246079004656908122275779849942744050813:ℚ)/22746766662597656250000000000000000000000000000000000000000000),((-63470164342440650127974231:ℚ)/221798400000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((7142500439:ℚ)/10000000000),((7326075673:ℚ)/10000000000),((353924327:ℚ)/58150000000),((8857499561:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3487438893:ℚ)/10000000000),((136670932024603542578340620480500105260352621710852317924142223:ℚ)/862950924607200000000000000000000000000000000000000000000000000),((-86576047047688805337184053:ℚ)/295731200000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((7262405053:ℚ)/10000000000),((3722920839:ℚ)/5000000000),((39026387:ℚ)/9850000000),((8737594947:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1495881039:ℚ)/5000000000),((15073947659613160445689529454353665243408716212059672953312997:ℚ)/95387534255192187500000000000000000000000000000000000000000000),((-88526705354721975783220237:ℚ)/295731200000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((7382272023:ℚ)/10000000000),((384263881:ℚ)/500000000),((-263881:ℚ)/2955000000),((8617727977:ℚ)/118200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((599856873:ℚ)/2500000000),((4907196947066285129327173029155336639848812355601513418181:ℚ)/30963760650000000000000000000000000000000000000000000000000),((-271436670953605006980962591:ℚ)/887193600000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((7621900189:ℚ)/10000000000),((8164006471:ℚ)/10000000000),((-484006471:ℚ)/61000000000),((8378099811:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((452571827820918463686357234601625800491717339336484487789:ℚ)/2837262500000000000000000000000000000000000000000000000000),((-162794903:ℚ)/512000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((1620155513:ℚ)/2000000000),((1259457441:ℚ)/1250000000),((-33273049:ℚ)/900000000),((526614829:ℚ)/8640000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((126485335848276127443104243106095704648033263319374577:ℚ)/755827200000000000000000000000000000000000000000000000),((-162794903:ℚ)/512000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((10012570663:ℚ)/10000000000),((13889288033:ℚ)/10000000000),((-6209288033:ℚ)/80000000000),((5987429337:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((194717219812593316315579386218125648269:ℚ)/1024000000000000000000000000000000000000),((-162794903:ℚ)/512000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC15
#check @N11Formalization.C450Source26GroupedC15.bound
#print axioms N11Formalization.C450Source26GroupedC15.valid0
#print axioms N11Formalization.C450Source26GroupedC15.valid1
#print axioms N11Formalization.C450Source26GroupedC15.valid2
#print axioms N11Formalization.C450Source26GroupedC15.valid3
#print axioms N11Formalization.C450Source26GroupedC15.valid4
#print axioms N11Formalization.C450Source26GroupedC15.valid5
#print axioms N11Formalization.C450Source26GroupedC15.valid6
#print axioms N11Formalization.C450Source26GroupedC15.valid7
#print axioms N11Formalization.C450Source26GroupedC15.valid8
#print axioms N11Formalization.C450Source26GroupedC15.valid9
#print axioms N11Formalization.C450Source26GroupedC15.valid10
#print axioms N11Formalization.C450Source26GroupedC15.valid11
#print axioms N11Formalization.C450Source26GroupedC15.bound
#print axioms N11Formalization.C450Source26GroupedC15.endpoint_checks
