import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((3123200939:ℚ)/5000000000),((6548061423:ℚ)/10000000000),((-4924184269:ℚ)/99200000000),((716799061:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3030333039:ℚ)/5000000000),((723099136373214444974024434832681467:ℚ)/3813248000000000000000000000000000000),((-17995849164284225745533399:ℚ)/92416000000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((3243323979:ℚ)/5000000000),((424253599:ℚ)/625000000),((-352760797:ℚ)/6437500000),((596676021:ℚ)/25750000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((685148457:ℚ)/1250000000),((78419765187827502606849971891034434892044710974120649:ℚ)/416842269897460937500000000000000000000000000000000000),((-57627169254840812334983237:ℚ)/277248000000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((1345339093:ℚ)/2000000000),((6907989231:ℚ)/10000000000),((-6003967693:ℚ)/106800000000),((190660907:ℚ)/10680000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((968211473:ℚ)/2000000000),((1414170271159517484131889563565363965320830108511672663:ℚ)/7613665200000000000000000000000000000000000000000000000),((-3268278215529832916588631:ℚ)/14786560000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((3423325699:ℚ)/5000000000),((7027879693:ℚ)/10000000000),((-6363639079:ℚ)/108700000000),((416674301:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4490148219:ℚ)/10000000000),((1452380701037272916515972791106052072372332261371125209:ℚ)/7839144915771484375000000000000000000000000000000000000),((-21037287861308028068410119:ℚ)/92416000000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((3483282643:ℚ)/5000000000),((3573865547:ℚ)/5000000000),((-3361596641:ℚ)/55300000000),((356717357:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((513964049:ℚ)/1250000000),((3489194967047913792075901827584575299222041801621261471:ℚ)/18874149218750000000000000000000000000000000000000000000),((-21648989529018442790401831:ℚ)/92416000000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((7086439301:ℚ)/10000000000),((7267545417:ℚ)/10000000000),((-7082636251:ℚ)/112500000000),((593560699:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3697264691:ℚ)/10000000000),((68416884492007908738600583498071398423966059903778561797:ℚ)/370788574218750000000000000000000000000000000000000000000),((-89047414119028466276480119:ℚ)/369664000000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((1441255093:ℚ)/2000000000),((738732451:ℚ)/1000000000),((-744197353:ℚ)/11440000000),((94744907:ℚ)/11440000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1616469179:ℚ)/5000000000),((430961677154353083581254146310183621477550611031177383:ℚ)/2339365600000000000000000000000000000000000000000000000),((-3660142219692394778932631:ℚ)/14786560000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((1831518917:ℚ)/2500000000),((3753535051:ℚ)/5000000000),((-3900605153:ℚ)/58150000000),((88481083:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((673250447:ℚ)/2500000000),((883181540939036837448441557671589190430308178262482343:ℚ)/4800530233764648437500000000000000000000000000000000000),((-5872775995610587837211191:ℚ)/23104000000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((7445841673:ℚ)/10000000000),((968308393:ℚ)/1250000000),((-1064925179:ℚ)/14775000000),((234158327:ℚ)/59100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((403513937:ℚ)/2000000000),((238498170740880754226755859993628048648270250744852751443:ℚ)/1290156693750000000000000000000000000000000000000000000000),((-96430026853615772749813951:ℚ)/369664000000000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((960646053:ℚ)/1250000000),((2056230967:ℚ)/2500000000),((-2488692901:ℚ)/30500000000),((-215351:ℚ)/2700000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((155630626094635102699498871971574939977673027536166009:ℚ)/833793750000000000000000000000000000000000000000000000),((-538931:ℚ)/2000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((8163405119:ℚ)/10000000000),((5067720363:ℚ)/5000000000),((-7843161089:ℚ)/64800000000),((-483405119:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((17140961238196438094475404060140388468648099836934035845943:ℚ)/86400000000000000000000000000000000000000000000000000000000),((-538931:ℚ)/2000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((314789191:ℚ)/312500000),((3486936229:ℚ)/2500000000),((-6780808687:ℚ)/40000000000),((-74789191:ℚ)/3450000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((14412677091348734359735776092570529452817721926506101:ℚ)/64161914062500000000000000000000000000000000000000000),((-538931:ℚ)/2000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC14
#check @N11Formalization.C450Source25GroupedC14.bound
#print axioms N11Formalization.C450Source25GroupedC14.valid0
#print axioms N11Formalization.C450Source25GroupedC14.valid1
#print axioms N11Formalization.C450Source25GroupedC14.valid2
#print axioms N11Formalization.C450Source25GroupedC14.valid3
#print axioms N11Formalization.C450Source25GroupedC14.valid4
#print axioms N11Formalization.C450Source25GroupedC14.valid5
#print axioms N11Formalization.C450Source25GroupedC14.valid6
#print axioms N11Formalization.C450Source25GroupedC14.valid7
#print axioms N11Formalization.C450Source25GroupedC14.valid8
#print axioms N11Formalization.C450Source25GroupedC14.valid9
#print axioms N11Formalization.C450Source25GroupedC14.valid10
#print axioms N11Formalization.C450Source25GroupedC14.valid11
#print axioms N11Formalization.C450Source25GroupedC14.bound
#print axioms N11Formalization.C450Source25GroupedC14.endpoint_checks
