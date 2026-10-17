import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((5831968889:ℚ)/10000000000),((3185072369:ℚ)/5000000000),((17021260741:ℚ)/35600000000),((3865072369:ℚ)/6200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3480379027:ℚ)/5000000000),((6703100316605009478329329:ℚ)/633680000000000000000000000),((-52918581635218213153689:ℚ)/180500000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((6308971723:ℚ)/10000000000),((1321700349:ℚ)/2000000000),((54402802061:ℚ)/110600000000),((1593700349:ℚ)/2670000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((184831053:ℚ)/312500000),((964630897130282587237566585317081789:ℚ)/183485400000000000000000000000000000000),((-8620897497316704808049:ℚ)/28880000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((261894773:ℚ)/400000000),((6846801529:ℚ)/10000000000),((2242863411:ℚ)/4576000000),((8206801529:ℚ)/13825000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((2662939001:ℚ)/5000000000),((37727047595012660958176477678737:ℚ)/8053760000000000000000000000000000),((-217194951059813597586009:ℚ)/722000000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((339285349:ℚ)/500000000),((6965931727:ℚ)/10000000000),((2886997443:ℚ)/5815000000),((8325931727:ℚ)/14300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2335741229:ℚ)/5000000000),((646487952032882690598510164535739:ℚ)/253606687500000000000000000000000000),((-219102615586914694418121:ℚ)/722000000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((863106897:ℚ)/1250000000),((3542524823:ℚ)/5000000000),((7321748279:ℚ)/14775000000),((4222524823:ℚ)/7268750000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((269397213:ℚ)/625000000),((145126771974638039184361006213969:ℚ)/60639062500000000000000000000000000),((-54981941303460361619321:ℚ)/180500000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((7023990509:ℚ)/10000000000),((7204155871:ℚ)/10000000000),((59407933563:ℚ)/120100000000),((8564155871:ℚ)/14775000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1959182593:ℚ)/5000000000),((488967188982133725474047571840726761:ℚ)/216360150000000000000000000000000000000),((-220748538815188355935209:ℚ)/722000000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((892889199:ℚ)/1250000000),((915406369:ℚ)/1250000000),((7530224393:ℚ)/15250000000),((1085406369:ℚ)/1876562500),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((348507717:ℚ)/1000000000),((2497807692622400139997993492693507:ℚ)/1162812500000000000000000000000000000),((-3461952218468908986689:ℚ)/11281250000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((7262225001:ℚ)/10000000000),((1488467081:ℚ)/2000000000),((61075575007:ℚ)/123900000000),((1760467081:ℚ)/3050000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((748141447:ℚ)/2500000000),((78926139707059033302383213148524423:ℚ)/38378025000000000000000000000000000000),((-8895079198712542855289:ℚ)/28880000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((1845331319:ℚ)/2500000000),((7561409713:ℚ)/10000000000),((15477319233:ℚ)/31450000000),((8921409713:ℚ)/15487500000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((120233189:ℚ)/500000000),((306682969578374394021844999996319:ℚ)/154547265625000000000000000000000000),((-223184657701451477902281:ℚ)/722000000000000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((3750207463:ℚ)/5000000000),((1949882423:ℚ)/2500000000),((10457150747:ℚ)/21600000000),((2289882423:ℚ)/3931250000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((810309069:ℚ)/5000000000),((7978184981787047598854098266061171:ℚ)/2332800000000000000000000000000000000),((-1179861381079101:ℚ)/3800000000000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((3869282113:ℚ)/5000000000),((2425856567:ℚ)/2500000000),((32204974791:ℚ)/80000000000),((921952189:ℚ)/1350000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((457327820325751347724994584292931377:ℚ)/24000000000000000000000000000000000000),((-2493901:ℚ)/8000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((4821322469:ℚ)/5000000000),((13507994781:ℚ)/10000000000),((38869257283:ℚ)/110400000000),((14867994781:ℚ)/20000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((215487673007091042094703201:ℚ)/6094080000000000000000000000),((-2493901:ℚ)/8000000)⟩
theorem valid11 : Valid source18 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source18 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC24
#check @N11Formalization.C450Source18GroupedC24.bound
#print axioms N11Formalization.C450Source18GroupedC24.valid0
#print axioms N11Formalization.C450Source18GroupedC24.valid1
#print axioms N11Formalization.C450Source18GroupedC24.valid2
#print axioms N11Formalization.C450Source18GroupedC24.valid3
#print axioms N11Formalization.C450Source18GroupedC24.valid4
#print axioms N11Formalization.C450Source18GroupedC24.valid5
#print axioms N11Formalization.C450Source18GroupedC24.valid6
#print axioms N11Formalization.C450Source18GroupedC24.valid7
#print axioms N11Formalization.C450Source18GroupedC24.valid8
#print axioms N11Formalization.C450Source18GroupedC24.valid9
#print axioms N11Formalization.C450Source18GroupedC24.valid10
#print axioms N11Formalization.C450Source18GroupedC24.valid11
#print axioms N11Formalization.C450Source18GroupedC24.bound
#print axioms N11Formalization.C450Source18GroupedC24.endpoint_checks
