import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((6838045289:ℚ)/10000000000),((7059848429:ℚ)/10000000000),((-59738332719:ℚ)/99200000000),((-1660681763:ℚ)/3370000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((1129041269:ℚ)/2500000000),((14334377702198988258243:ℚ)/44362890625000000000000),((1292061702125949282142241937:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((6957971039:ℚ)/10000000000),((3559876571:ℚ)/5000000000),((-30198642281:ℚ)/50550000000),((-5101971039:ℚ)/10205000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((4139914181:ℚ)/10000000000),((42060096351465478726962934046297107363:ℚ)/131609484093750000000000000000000000000),((1281256649896156504534303937:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((3508958629:ℚ)/5000000000),((1794911989:ℚ)/2500000000),((-15264031879:ℚ)/25512500000),((-2580958629:ℚ)/5150000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((984809467:ℚ)/2500000000),((22263896343636580441867271588695247130184444250505854519:ℚ)/69695493968750000000000000000000000000000000000000000000),((318947702935011450970543577:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7077852791:ℚ)/10000000000),((3619766573:ℚ)/5000000000),((-30857432303:ℚ)/51500000000),((-1740617597:ℚ)/3465000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((58256327:ℚ)/156250000),((1237219862942065864597500817901897402400678227723507:ℚ)/3874567483520507812500000000000000000000000000000000),((1270282759001871204249653457:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((3568888967:ℚ)/5000000000),((7299408977:ℚ)/10000000000),((-2970166607:ℚ)/4950000000),((-2640888967:ℚ)/5245000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3505577747:ℚ)/10000000000),((28498096961180467934199796533377016115171442976378823463:ℚ)/89279487696093750000000000000000000000000000000000000000),((316183121814517806306221233:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((3598846489:ℚ)/5000000000),((7359275707:ℚ)/10000000000),((-63032032777:ℚ)/104900000000),((-2670846489:ℚ)/5292500000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((3268298113:ℚ)/10000000000),((310138503006900298800446826909749136475530876578868187651:ℚ)/971936978323925781250000000000000000000000000000000000000),((314784997924166192830641137:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((7257598197:ℚ)/10000000000),((7419133581:ℚ)/10000000000),((-63690469391:ℚ)/105850000000),((-5401598197:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((3013147407:ℚ)/10000000000),((47607386720833175691182260234381026621782923512832778657:ℚ)/149241937300000000000000000000000000000000000000000000000),((3760515804806004897747850219:ℚ)/8871936000000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((3658746929:ℚ)/5000000000),((7538823709:ℚ)/10000000000),((-65007060799:ℚ)/106800000000),((-2730746929:ℚ)/5435000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((109404881:ℚ)/400000000),((86243633466514145500588462238687734992766580961822361897:ℚ)/267910616641406250000000000000000000000000000000000000000),((311957078199560065746929377:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((743725753:ℚ)/1000000000),((1914620291:ℚ)/2500000000),((-16580823201:ℚ)/27175000000),((-558125753:ℚ)/1106000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2073178489:ℚ)/10000000000),((184807723101517705673098950784926507932238273644043669:ℚ)/574453605621875000000000000000000000000000000000000000),((12363476894147385774151473:ℚ)/29573120000000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((7556985943:ℚ)/10000000000),((1579540933:ℚ)/2000000000),((-13790950263:ℚ)/22120000000),((-5700985943:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((532216649:ℚ)/5000000000),((9111181947713495699907012435340640241:ℚ)/27835808000000000000000000000000000000),((1224698091217197968402004753:ℚ)/2957312000000000000000000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((7796344127:ℚ)/10000000000),((8853578841:ℚ)/10000000000),((-79469367251:ℚ)/114400000000),((-1980114709:ℚ)/4320000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((266737523742953558629635837286169231:ℚ)/741312000000000000000000000000000000),((422600671:ℚ)/1024000000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((8752676571:ℚ)/10000000000),((215239143:ℚ)/200000000),((-2009230573:ℚ)/2592000000),((-6896676571:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((10200171855912802925763618937108174931:ℚ)/25920000000000000000000000000000000000),((422600671:ℚ)/1024000000)⟩
theorem valid11 : Valid source30 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((10661706679:ℚ)/10000000000),((1457176609:ℚ)/1000000000),((-14236942699:ℚ)/16000000000),((-8805706679:ℚ)/22080000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((36903991804645501680020627:ℚ)/81254400000000000000000000),((422600671:ℚ)/1024000000)⟩
theorem valid12 : Valid source30 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source30 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source30 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source30 nn0 nn1 Qcell ((2117:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source30 nn0 nn1 Qcell ((2117:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC06
#check @N11Formalization.C450Source30GroupedC06.bound
#print axioms N11Formalization.C450Source30GroupedC06.valid0
#print axioms N11Formalization.C450Source30GroupedC06.valid1
#print axioms N11Formalization.C450Source30GroupedC06.valid2
#print axioms N11Formalization.C450Source30GroupedC06.valid3
#print axioms N11Formalization.C450Source30GroupedC06.valid4
#print axioms N11Formalization.C450Source30GroupedC06.valid5
#print axioms N11Formalization.C450Source30GroupedC06.valid6
#print axioms N11Formalization.C450Source30GroupedC06.valid7
#print axioms N11Formalization.C450Source30GroupedC06.valid8
#print axioms N11Formalization.C450Source30GroupedC06.valid9
#print axioms N11Formalization.C450Source30GroupedC06.valid10
#print axioms N11Formalization.C450Source30GroupedC06.valid11
#print axioms N11Formalization.C450Source30GroupedC06.valid12
#print axioms N11Formalization.C450Source30GroupedC06.bound
#print axioms N11Formalization.C450Source30GroupedC06.endpoint_checks
