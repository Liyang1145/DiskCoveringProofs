import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((355529907:ℚ)/625000000),((1247789517:ℚ)/2000000000),((455529907:ℚ)/834375000),((13918105653:ℚ)/19840000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7250232339:ℚ)/10000000000),((-1685071801376141494732085384953:ℚ)/72609569549560546875000000000000),((-317661589133207413129441:ℚ)/866400000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((3083135531:ℚ)/5000000000),((6477692657:ℚ)/10000000000),((3883135531:ℚ)/6912500000),((23913077971:ℚ)/35600000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6243359827:ℚ)/10000000000),((-109517959410532663505918305636287831311140496232958679:ℚ)/3096540106201171875000000000000000000000000000000000000),((-2682797959337312543943177:ℚ)/7220000000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((3202511131:ℚ)/5000000000),((3358177203:ℚ)/5000000000),((4002511131:ℚ)/7150000000),((36943594827:ℚ)/55300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5683948381:ℚ)/10000000000),((-41036102307236077888342960454160375614871260084636917:ℚ)/1142268359375000000000000000000000000000000000000000000),((-4036672139012335596093467:ℚ)/10830000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((3321844863:ℚ)/5000000000),((6835656611:ℚ)/10000000000),((4121844863:ℚ)/7268750000),((74960909499:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5070729201:ℚ)/10000000000),((-36895104523587708430506638794222211695013228249565763:ℚ)/900099418830871582031250000000000000000000000000000000),((-2708324408894846062718633:ℚ)/7220000000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((3381497323:ℚ)/5000000000),((434683809:ℚ)/625000000),((1393832441:ℚ)/2462500000),((4752154281:ℚ)/7268750000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2368705979:ℚ)/5000000000),((-1436048713247836959362423599672066539328306736977621:ℚ)/34997740173339843750000000000000000000000000000000000),((-4068097560099656258659817:ℚ)/10830000000000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((1376456321:ℚ)/2000000000),((7074208259:ℚ)/10000000000),((1696456321:ℚ)/3002500000),((25702624777:ℚ)/39400000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4380904427:ℚ)/10000000000),((-10415887578167197015929022323978325038562520310403829:ℚ)/253758339990234375000000000000000000000000000000000000),((-339454965072813741532561:ℚ)/902500000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((7001551463:ℚ)/10000000000),((7193459359:ℚ)/10000000000),((8601551463:ℚ)/15250000000),((78181134231:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3994969577:ℚ)/10000000000),((-454770354224872752018074835761509225584672490069848241:ℚ)/11083056640625000000000000000000000000000000000000000000),((-1359524274969675485763569:ℚ)/3610000000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((3560402513:ℚ)/5000000000),((1857978969:ℚ)/2500000000),((4360402513:ℚ)/7862500000),((20081810721:ℚ)/30500000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((892510041:ℚ)/2500000000),((-13940954556899887517789666303212391591435647653794911:ℚ)/379727461242675781250000000000000000000000000000000000),((-4068116755610223623991347:ℚ)/10830000000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((7359266241:ℚ)/10000000000),((7670315981:ℚ)/10000000000),((8959266241:ℚ)/16200000000),((82472843829:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((63091347:ℚ)/250000000),((-18072133202105704089353000002574126535152820326030341:ℚ)/492075000000000000000000000000000000000000000000000000),((-367020195498129523:ℚ)/972800000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((7597670767:ℚ)/10000000000),((9575971133:ℚ)/10000000000),((9197670767:ℚ)/20000000000),((33207913399:ℚ)/43200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((247585819:ℚ)/10000000000),((7644762400785822271469329935157073:ℚ)/1500000000000000000000000000000000000),((-370600746108431901:ℚ)/972800000000000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((4751676829:ℚ)/5000000000),((6691298863:ℚ)/5000000000),((1850558943:ℚ)/4600000000),((66941689767:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((444005341613108526100361:ℚ)/10580000000000000000000000),((-48767859:ℚ)/128000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC25
#check @N11Formalization.C450Source22GroupedC25.bound
#print axioms N11Formalization.C450Source22GroupedC25.valid0
#print axioms N11Formalization.C450Source22GroupedC25.valid1
#print axioms N11Formalization.C450Source22GroupedC25.valid2
#print axioms N11Formalization.C450Source22GroupedC25.valid3
#print axioms N11Formalization.C450Source22GroupedC25.valid4
#print axioms N11Formalization.C450Source22GroupedC25.valid5
#print axioms N11Formalization.C450Source22GroupedC25.valid6
#print axioms N11Formalization.C450Source22GroupedC25.valid7
#print axioms N11Formalization.C450Source22GroupedC25.valid8
#print axioms N11Formalization.C450Source22GroupedC25.valid9
#print axioms N11Formalization.C450Source22GroupedC25.valid10
#print axioms N11Formalization.C450Source22GroupedC25.bound
#print axioms N11Formalization.C450Source22GroupedC25.endpoint_checks
