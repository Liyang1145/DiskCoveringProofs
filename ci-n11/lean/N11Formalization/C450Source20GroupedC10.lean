import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((51471743:ℚ)/80000000),((3366810987:ℚ)/5000000000),((-17807676909:ℚ)/49600000000),((-105775229:ℚ)/412000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5612795839:ℚ)/10000000000),((1657624783764783094607365988469205278411080853597143:ℚ)/20324722200000000000000000000000000000000000000000000),((14465715548316961951439:ℚ)/118292480000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((6672804559:ℚ)/10000000000),((3426517257:ℚ)/5000000000),((-18225620799:ℚ)/51500000000),((-13938413677:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((9748581:ℚ)/19531250),((920430986380480031844117923553192771393057008981720016349:ℚ)/11610842465527343750000000000000000000000000000000000000000),((215245960822091564528929391:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((1698046573:ℚ)/2500000000),((6972423289:ℚ)/10000000000),((-37286963023:ℚ)/104900000000),((-3574139719:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4652515813:ℚ)/10000000000),((154284641061103452794118698940195433212789831807736743689:ℚ)/1949886424511718750000000000000000000000000000000000000000),((13114182394943198941988519:ℚ)/115520000000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((55292363:ℚ)/80000000),((7091789559:ℚ)/10000000000),((-12707508971:ℚ)/35600000000),((-117237089:ℚ)/434800000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4289237869:ℚ)/10000000000),((1805758743614120168618480374561496385840308114694439:ℚ)/22861705953400000000000000000000000000000000000000000),((13080878850184516086359:ℚ)/118292480000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((7030883007:ℚ)/10000000000),((446966539:ℚ)/625000000),((-2408765773:ℚ)/6793750000),((-15012649021:ℚ)/54825000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3894548423:ℚ)/10000000000),((3637935473429479530251364977835371633727618341798565913831:ℚ)/46648130220373535156250000000000000000000000000000000000000),((198931358517616538040495439:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((709054413:ℚ)/1000000000),((225347953:ℚ)/312500000),((-71613863:ℚ)/201562500),((-1519163239:ℚ)/5530000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3682289203:ℚ)/10000000000),((83018716134660855744950257594945900962573772015878401:ℚ)/1065209796533203125000000000000000000000000000000000000),((1961954638288959935125159:ℚ)/18483200000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((7150200303:ℚ)/10000000000),((7270799309:ℚ)/10000000000),((-39375595163:ℚ)/110600000000),((-15370600909:ℚ)/55775000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((864417129:ℚ)/2500000000),((1459634451587584063193901851912907652797891900986844153507:ℚ)/18740186438668823242187500000000000000000000000000000000000),((193454757370251416862618799:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((3604925827:ℚ)/5000000000),((916307399:ℚ)/1250000000),((-4974151793:ℚ)/13943750000),((-7774777481:ℚ)/28125000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3218093891:ℚ)/10000000000),((141487102025630397051245874312113535781469869410615760987:ℚ)/1817642524838447570800781250000000000000000000000000000000),((47677308624789572679634119:ℚ)/462080000000000000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((1453899661:ℚ)/2000000000),((7449764663:ℚ)/10000000000),((-40628352641:ℚ)/112500000000),((-3145698983:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2959931069:ℚ)/10000000000),((3310594871957828786611365618165151130704004647975577657:ℚ)/42108580800000000000000000000000000000000000000000000000),((7518355632266744782488231:ℚ)/73932800000000000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((7388777983:ℚ)/10000000000),((3784525931:ℚ)/5000000000),((-20731681517:ℚ)/57200000000),((-16086333949:ℚ)/58150000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((47262729:ℚ)/200000000),((530681852422725779236680948603925432271348499506901753649:ℚ)/6759146569140625000000000000000000000000000000000000000000),((182443723671049603187248079:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((7508040241:ℚ)/10000000000),((7688321677:ℚ)/10000000000),((-42298251739:ℚ)/116300000000),((-16444120723:ℚ)/59100000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1557205761:ℚ)/10000000000),((544693355993070268501654620609179286133154019031915561077:ℚ)/6946538124218750000000000000000000000000000000000000000000),((176909223219245620101178991:ℚ)/1848320000000000000000000000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/16),((-3:ℚ)/8),((7627285927:ℚ)/10000000000),((792681243:ℚ)/1000000000),((-1465589567:ℚ)/3940000000),((-16801857781:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((33459654916254086879613965988248875790485896292420024216109:ℚ)/419205534375000000000000000000000000000000000000000000000000),((5977423:ℚ)/64000000)⟩
theorem valid11 : Valid source20 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source20 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((3932865353:ℚ)/5000000000),((2100904663:ℚ)/2500000000),((-11826332641:ℚ)/30500000000),((-8758596059:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((177936484740817422229617984725184812229823667563515171827:ℚ)/2161193400000000000000000000000000000000000000000000000000),((5977423:ℚ)/64000000)⟩
theorem valid12 : Valid source20 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((2085613289:ℚ)/2500000000),((2061824097:ℚ)/2000000000),((-4042922893:ℚ)/8640000000),((-4736839867:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((64217413621045049505648720689868123187226160299178682919:ℚ)/675000000000000000000000000000000000000000000000000000000),((5977423:ℚ)/64000000)⟩
theorem valid13 : Valid source20 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((10247700133:ℚ)/10000000000),((705778387:ℚ)/500000000),((-4364448709:ℚ)/8000000000),((-1072308713:ℚ)/4800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((28375580110882094826514993786597879082984826319718549:ℚ)/259200000000000000000000000000000000000000000000000000),((5977423:ℚ)/64000000)⟩
theorem valid14 : Valid source20 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source20 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((2231:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source20 nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source20 nn0 nn1 Qcell ((2231:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source20 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC10
#check @N11Formalization.C450Source20GroupedC10.bound
#print axioms N11Formalization.C450Source20GroupedC10.valid0
#print axioms N11Formalization.C450Source20GroupedC10.valid1
#print axioms N11Formalization.C450Source20GroupedC10.valid2
#print axioms N11Formalization.C450Source20GroupedC10.valid3
#print axioms N11Formalization.C450Source20GroupedC10.valid4
#print axioms N11Formalization.C450Source20GroupedC10.valid5
#print axioms N11Formalization.C450Source20GroupedC10.valid6
#print axioms N11Formalization.C450Source20GroupedC10.valid7
#print axioms N11Formalization.C450Source20GroupedC10.valid8
#print axioms N11Formalization.C450Source20GroupedC10.valid9
#print axioms N11Formalization.C450Source20GroupedC10.valid10
#print axioms N11Formalization.C450Source20GroupedC10.valid11
#print axioms N11Formalization.C450Source20GroupedC10.valid12
#print axioms N11Formalization.C450Source20GroupedC10.valid13
#print axioms N11Formalization.C450Source20GroupedC10.valid14
#print axioms N11Formalization.C450Source20GroupedC10.bound
#print axioms N11Formalization.C450Source20GroupedC10.endpoint_checks
