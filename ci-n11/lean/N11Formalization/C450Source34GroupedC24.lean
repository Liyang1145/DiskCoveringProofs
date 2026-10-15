import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((7:ℚ)/16),((1:ℚ)/2),((169803177:ℚ)/312500000),((1443441787:ℚ)/2500000000),((1828622239:ℚ)/3218750000),((2103441787:ℚ)/3100000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7742283673:ℚ)/10000000000),((-19901207052832297858127597679755939068770680500580821559:ℚ)/57533868750000000000000000000000000000000000000000000000),((-376024685477224494589039:ℚ)/902500000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((5675187939:ℚ)/10000000000),((1503753803:ℚ)/2500000000),((60206315573:ℚ)/106800000000),((2163753803:ℚ)/3218750000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7276563627:ℚ)/10000000000),((-4775234131899448154174470974465263470016754719690242793:ℚ)/13912110757827758789062500000000000000000000000000000000),((-19623712927971189900141:ℚ)/47500000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((2958191941:ℚ)/5000000000),((3067769373:ℚ)/5000000000),((30947343587:ℚ)/54350000000),((1462589791:ℚ)/2225000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((6785692579:ℚ)/10000000000),((-26092946435284920894869669475249580239206578026509906929:ℚ)/74834111621093750000000000000000000000000000000000000000),((-4480787511655883644476797:ℚ)/10830000000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((188652587:ℚ)/312500000),((6256000021:ℚ)/10000000000),((1960568109:ℚ)/3456250000),((8896000021:ℚ)/13587500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((652897911:ℚ)/1000000000),((-20162411390036923980982930722384801035033557735127178641:ℚ)/58058667032432556152343750000000000000000000000000000000),((-312940047261409668049109:ℚ)/760000000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/16),((1:ℚ)/2),((615732031:ℚ)/1000000000),((6376402281:ℚ)/10000000000),((2119374739:ℚ)/3750000000),((9016402281:ℚ)/13825000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1252695819:ℚ)/2000000000),((-66951818715435591033953811820560260156556179294785651:ℚ)/193533756637573242187500000000000000000000000000000000),((-17748293591202057721937573:ℚ)/43320000000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((6277699657:ℚ)/10000000000),((3248374273:ℚ)/5000000000),((64423897599:ℚ)/114400000000),((4568374273:ℚ)/7031250000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2993995377:ℚ)/5000000000),((-107084487577752845099163620035345376811536297333659208887:ℚ)/310680270195007324218750000000000000000000000000000000000),((-77435465110642732795421:ℚ)/190000000000000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((31990119:ℚ)/50000000),((6617041633:ℚ)/10000000000),((326330833:ℚ)/581500000),((9257041633:ℚ)/14300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2850516407:ℚ)/5000000000),((-663698496133311698286557737543536945717644260048059279193:ℚ)/1932302693750000000000000000000000000000000000000000000000),((-5852854377470655578429959:ℚ)/14440000000000000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((6518295517:ℚ)/10000000000),((1684321043:ℚ)/2500000000),((22036022873:ℚ)/39400000000),((2344321043:ℚ)/3634375000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((337546457:ℚ)/625000000),((-5058572219466792926502184155870230277650188404309990023:ℚ)/14776632125806808471679687500000000000000000000000000000),((-363710994280765184784919:ℚ)/902500000000000000000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((3319258699:ℚ)/5000000000),((6857478621:ℚ)/10000000000),((33474810893:ℚ)/60050000000),((3165826207:ℚ)/4925000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((5084726001:ℚ)/10000000000),((-1164980207939288808693400122281257953455295664847610529:ℚ)/3413789721679687500000000000000000000000000000000000000),((-17353982504337324400730813:ℚ)/43320000000000000000000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((1689672967:ℚ)/2500000000),((3488813641:ℚ)/5000000000),((16947710769:ℚ)/30500000000),((4808813641:ℚ)/7506250000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1187451677:ℚ)/2500000000),((-164581918952559204395202297876870623346964701916324561151:ℚ)/483726835606384277343750000000000000000000000000000000000),((-1437177497909220021598711:ℚ)/3610000000000000000000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((859852649:ℚ)/1250000000),((1864451297:ℚ)/2500000000),((953218727:ℚ)/1800000000),((2524451297:ℚ)/3812500000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((27447659:ℚ)/62500000),((-1001355253889628964551402720674412818288981532173787209:ℚ)/3117109680175781250000000000000000000000000000000000000),((-342807730300504212539079:ℚ)/902500000000000000000000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((7358927607:ℚ)/10000000000),((187470783:ℚ)/200000000),((71992493249:ℚ)/160000000000),((80090261:ℚ)/108000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((631359431:ℚ)/2500000000),((-6134317050492447835105408549728649611964742659471:ℚ)/23619600000000000000000000000000000000000000000000),((-5827207526931519:ℚ)/15200000000000000)⟩
theorem valid11 : Valid source34 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((74195561:ℚ)/80000000),((13191916233:ℚ)/10000000000),((227736309:ℚ)/588800000),((15831916233:ℚ)/20000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-60679356145796141902637308039313451554313855862857859407:ℚ)/287500000000000000000000000000000000000000000000000000000),((-310687:ℚ)/800000)⟩
theorem valid12 : Valid source34 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source34 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source34 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC24
#check @N11Formalization.C450Source34GroupedC24.bound
#print axioms N11Formalization.C450Source34GroupedC24.valid0
#print axioms N11Formalization.C450Source34GroupedC24.valid1
#print axioms N11Formalization.C450Source34GroupedC24.valid2
#print axioms N11Formalization.C450Source34GroupedC24.valid3
#print axioms N11Formalization.C450Source34GroupedC24.valid4
#print axioms N11Formalization.C450Source34GroupedC24.valid5
#print axioms N11Formalization.C450Source34GroupedC24.valid6
#print axioms N11Formalization.C450Source34GroupedC24.valid7
#print axioms N11Formalization.C450Source34GroupedC24.valid8
#print axioms N11Formalization.C450Source34GroupedC24.valid9
#print axioms N11Formalization.C450Source34GroupedC24.valid10
#print axioms N11Formalization.C450Source34GroupedC24.valid11
#print axioms N11Formalization.C450Source34GroupedC24.valid12
#print axioms N11Formalization.C450Source34GroupedC24.bound
#print axioms N11Formalization.C450Source34GroupedC24.endpoint_checks
