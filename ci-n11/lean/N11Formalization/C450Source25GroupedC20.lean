import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((1472481647:ℚ)/2500000000),((6441045289:ℚ)/10000000000),((8097444941:ℚ)/26700000000),((10281045289:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((427560323:ℚ)/625000000),((21871419388474213054505378644798047409687:ℚ)/271842636672000000000000000000000000000000),((-16585068966734130323821413:ℚ)/46208000000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((6369964067:ℚ)/10000000000),((6680675361:ℚ)/10000000000),((4832841743:ℚ)/15800000000),((3506891787:ℚ)/8900000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((576907949:ℚ)/1000000000),((1952117061014647052781162518309615621810008218500116952343:ℚ)/27498197056250000000000000000000000000000000000000000000000),((-52347906055272198793485439:ℚ)/138624000000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((3304859713:ℚ)/5000000000),((6800435741:ℚ)/10000000000),((17274579139:ℚ)/56250000000),((10640435741:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5162022887:ℚ)/10000000000),((102518463361891216795323263614447882539989800807102774847:ℚ)/1528806086718750000000000000000000000000000000000000000000),((-17878985064951560805204093:ℚ)/46208000000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((672953919:ℚ)/1000000000),((216255067:ℚ)/312500000),((3490861757:ℚ)/11440000000),((336255067:ℚ)/878906250),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4833011659:ℚ)/10000000000),((123674641756441402763806152965884230289430505370302177079:ℚ)/1851136609911918640136718750000000000000000000000000000000),((-1102083961491978052687:ℚ)/2820312500000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((1369864591:ℚ)/2000000000),((3519928131:ℚ)/5000000000),((7053593773:ℚ)/23260000000),((494538921:ℚ)/1300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4482043307:ℚ)/10000000000),((309332414801486642460904039239618536646055739446460784429:ℚ)/4643115770312500000000000000000000000000000000000000000000),((-13674578929817568607042999:ℚ)/34656000000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((1393814503:ℚ)/2000000000),((7159519677:ℚ)/10000000000),((7125443509:ℚ)/23640000000),((10999519677:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4103450563:ℚ)/10000000000),((99098154153207400031656384195562665102274829910102288863033:ℚ)/1490430222737377929687500000000000000000000000000000000000000),((-55223021055597339852953911:ℚ)/138624000000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((3544394773:ℚ)/5000000000),((7279153867:ℚ)/10000000000),((17993184319:ℚ)/60050000000),((11119153867:ℚ)/29550000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1844348741:ℚ)/5000000000),((15448204885191284299930584680361260417765809654811239153531823:ℚ)/232615413152711718750000000000000000000000000000000000000000000),((-18581252490543754618228717:ℚ)/46208000000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((3604237809:ℚ)/5000000000),((3699380109:ℚ)/5000000000),((18172713427:ℚ)/61000000000),((5619380109:ℚ)/15012500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((402976689:ℚ)/1250000000),((5223423111929746435940719608796199725462844751292238285809:ℚ)/78686231925305175781250000000000000000000000000000000000000),((-14065133720450763440147479:ℚ)/34656000000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((3664066099:ℚ)/5000000000),((492308253:ℚ)/625000000),((18352198297:ℚ)/64800000000),((732308253:ℚ)/1906250000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((2682812369:ℚ)/10000000000),((1315956315894081599737382983686001992012365554852833503:ℚ)/17752913725376129150390625000000000000000000000000000000),((-12414171316245661:ℚ)/30400000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((1561297983:ℚ)/2000000000),((9786584109:ℚ)/10000000000),((7627893949:ℚ)/32000000000),((1514064901:ℚ)/3600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1762526720417087052694489365201569090792076911907329:ℚ)/18225000000000000000000000000000000000000000000000000),((-6730681:ℚ)/16000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((242917657:ℚ)/250000000),((1699734959:ℚ)/1250000000),((1096752971:ℚ)/5520000000),((2179734959:ℚ)/5000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((20275035543822675531642725034118631233:ℚ)/148781250000000000000000000000000000000),((-6730681:ℚ)/16000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC20
#check @N11Formalization.C450Source25GroupedC20.bound
#print axioms N11Formalization.C450Source25GroupedC20.valid0
#print axioms N11Formalization.C450Source25GroupedC20.valid1
#print axioms N11Formalization.C450Source25GroupedC20.valid2
#print axioms N11Formalization.C450Source25GroupedC20.valid3
#print axioms N11Formalization.C450Source25GroupedC20.valid4
#print axioms N11Formalization.C450Source25GroupedC20.valid5
#print axioms N11Formalization.C450Source25GroupedC20.valid6
#print axioms N11Formalization.C450Source25GroupedC20.valid7
#print axioms N11Formalization.C450Source25GroupedC20.valid8
#print axioms N11Formalization.C450Source25GroupedC20.valid9
#print axioms N11Formalization.C450Source25GroupedC20.valid10
#print axioms N11Formalization.C450Source25GroupedC20.bound
#print axioms N11Formalization.C450Source25GroupedC20.endpoint_checks
