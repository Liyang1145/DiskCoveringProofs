import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((6995582829:ℚ)/10000000000),((3612480167:ℚ)/5000000000),((-38002242171:ℚ)/49600000000),((-16346748487:ℚ)/25275000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((803022547:ℚ)/2000000000),((168357425453631821497484540912721871:ℚ)/448508824218750000000000000000000000),((6115958273028296641285356749:ℚ)/8871936000000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((3557586713:ℚ)/5000000000),((1821168771:ℚ)/2500000000),((-19195194023:ℚ)/25275000000),((-8352760139:ℚ)/12756250000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((718236773:ℚ)/2000000000),((303520556097574929831261589469977814869837185522579988051:ℚ)/819747793686962127685546875000000000000000000000000000000),((509319499165787588239527847:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((1434991373:ℚ)/2000000000),((3672191757:ℚ)/5000000000),((-38778492841:ℚ)/51025000000),((-3376974119:ℚ)/5150000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((3360236461:ℚ)/10000000000),((25786554785620117071106181072509454953932103849345280389:ℚ)/69695493968750000000000000000000000000000000000000000000),((81512813380140956949719727:ℚ)/118292480000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((7234732693:ℚ)/10000000000),((37020429:ℚ)/50000000),((-391665577:ℚ)/515000000),((-17064198079:ℚ)/25987500000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((1556462077:ℚ)/5000000000),((201451162212051864640211435116590457470708190738704067:ℚ)/544861052370071411132812500000000000000000000000000000),((2038346218388131890590816287:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((3647250561:ℚ)/5000000000),((7463782109:ℚ)/10000000000),((-11301309631:ℚ)/14850000000),((-8621751683:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((284497621:ℚ)/1000000000),((1546273953600020307526344742047013448980103709381099317761:ℚ)/4184975985754394531250000000000000000000000000000000000000),((1529141740872593514669142469:ℚ)/2217984000000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((1470852471:ℚ)/2000000000),((1895789361:ℚ)/2500000000),((-20165261693:ℚ)/26225000000),((-3484557413:ℚ)/5340000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((637472213:ℚ)/2500000000),((41433736729970541374733434786096533211882534083135338407:ℚ)/110926872150000000000000000000000000000000000000000000000),((245022713313007049287608149:ℚ)/354877440000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((1868441003:ℚ)/2500000000),((977730397:ℚ)/1250000000),((-10470495161:ℚ)/13350000000),((-4445323009:ℚ)/6912500000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1825167677:ℚ)/10000000000),((210155072647311220122068044981463732149419138329129390617:ℚ)/551184138903808593750000000000000000000000000000000000000),((127405363084541318001387167:ℚ)/184832000000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((1542537831:ℚ)/2000000000),((503778099:ℚ)/625000000),((-5429115287:ℚ)/6912500000),((-3699613493:ℚ)/5720000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((245861219581413126804305237548359676486485707111361213631:ℚ)/646834588400000000000000000000000000000000000000000000000),((140866133:ℚ)/204800000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((7951518823:ℚ)/10000000000),((1802844527:ℚ)/2000000000),((-19852978851:ℚ)/22880000000),((-19214556469:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((119041028940137821513117590774401854124732197874433944899:ℚ)/281466900000000000000000000000000000000000000000000000000),((140866133:ℚ)/204800000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((2226513079:ℚ)/2500000000),((2183921823:ℚ)/2000000000),((-24806983699:ℚ)/25920000000),((-5519539237:ℚ)/10000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((14674028034280695890277066514384091747532804678291018823:ℚ)/31640625000000000000000000000000000000000000000000000000),((140866133:ℚ)/204800000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((5406261123:ℚ)/5000000000),((1472592143:ℚ)/1000000000),(-1:ℚ),((-13898783369:ℚ)/27600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((289133555389227058926389252442084113:ℚ)/584016000000000000000000000000000000),((140866133:ℚ)/204800000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source30 nn0 nn1 Qcell ((2041:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source30 nn0 nn1 Qcell ((1049:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source30 nn0 nn1 Qcell ((1049:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC04
#check @N11Formalization.C450Source30GroupedC04.bound
#print axioms N11Formalization.C450Source30GroupedC04.valid0
#print axioms N11Formalization.C450Source30GroupedC04.valid1
#print axioms N11Formalization.C450Source30GroupedC04.valid2
#print axioms N11Formalization.C450Source30GroupedC04.valid3
#print axioms N11Formalization.C450Source30GroupedC04.valid4
#print axioms N11Formalization.C450Source30GroupedC04.valid5
#print axioms N11Formalization.C450Source30GroupedC04.valid6
#print axioms N11Formalization.C450Source30GroupedC04.valid7
#print axioms N11Formalization.C450Source30GroupedC04.valid8
#print axioms N11Formalization.C450Source30GroupedC04.valid9
#print axioms N11Formalization.C450Source30GroupedC04.valid10
#print axioms N11Formalization.C450Source30GroupedC04.bound
#print axioms N11Formalization.C450Source30GroupedC04.endpoint_checks
