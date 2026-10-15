import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((163937641:ℚ)/250000000),((6773034813:ℚ)/10000000000),((-27571243691:ℚ)/99200000000),((-235812923:ℚ)/1263750000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2649776279:ℚ)/5000000000),((556368270824684389878150718030021952917:ℚ)/3050598400000000000000000000000000000000),((124312791541321891458597:ℚ)/1155200000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((6678310433:ℚ)/10000000000),((1723441787:ℚ)/2500000000),((-7104092509:ℚ)/25275000000),((-9794931299:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((199044691:ℚ)/400000000),((115640296346932336238986110206489678741048260677239693:ℚ)/630715534057617187500000000000000000000000000000000000),((185203906574428675725319093:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((6799037513:ℚ)/10000000000),((6954105473:ℚ)/10000000000),((-28838738311:ℚ)/103000000000),((-1451016077:ℚ)/7425000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((4632382231:ℚ)/10000000000),((484615030448456117254160569566388200960804747336985983:ℚ)/2667790527343750000000000000000000000000000000000000000),((171372052735228268420133253:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((6859373287:ℚ)/10000000000),((7014425931:ℚ)/10000000000),((-29260981517:ℚ)/103950000000),((-10338119861:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((445142963:ℚ)/1000000000),((79082793453274750448387418362243437678256266789336333:ℚ)/434153671875000000000000000000000000000000000000000000),((164405318193198490488223653:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((3459845621:ℚ)/5000000000),((3537364509:ℚ)/5000000000),((-14841551563:ℚ)/52450000000),((-5259536863:ℚ)/26462500000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((6821429:ℚ)/16000000),((16471475503940801950023514753662275732166150262608057011:ℚ)/90181300703125000000000000000000000000000000000000000000),((39351168894827552988576717:ℚ)/462080000000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((6979991873:ℚ)/10000000000),((1783753803:ℚ)/2500000000),((-7526276621:ℚ)/26462500000),((-10699975619:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((4067284491:ℚ)/10000000000),((1590788329876575740139879689346710635791531184726182071:ℚ)/8686281383972167968750000000000000000000000000000000000),((150370098870030200050262773:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-7:ℚ)/16),((-3:ℚ)/8),((7040275657:ℚ)/10000000000),((7195284973:ℚ)/10000000000),((-10175664937:ℚ)/35600000000),((-10880826971:ℚ)/53875000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((965467043:ℚ)/2500000000),((15533813882096724649552406250500987739675371328731590963:ℚ)/84596280000000000000000000000000000000000000000000000000),((143301562968601216821563013:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((7100543053:ℚ)/10000000000),((3627769373:ℚ)/5000000000),((-15474385611:ℚ)/53875000000),((-11061629159:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((45569561:ℚ)/125000000),((17993002466555202132563328792298504635626619773950356003:ℚ)/97733143310546875000000000000000000000000000000000000000),((136199043759488589724671933:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((7160794503:ℚ)/10000000000),((7315776957:ℚ)/10000000000),((-31370438699:ℚ)/108700000000),((-661316677:ℚ)/3225000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((341630079:ℚ)/1000000000),((27781390168245990752435241151579046708603843160404033321:ℚ)/150511582382812500000000000000000000000000000000000000000),((129062518044016681657151333:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((3610515217:ℚ)/5000000000),((7376000021:ℚ)/10000000000),((-31792000147:ℚ)/109650000000),((-815935093:ℚ)/3950000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3171259279:ℚ)/10000000000),((3545943567881423906596912017727063149231459233122923617:ℚ)/19161851484375000000000000000000000000000000000000000000),((30472990838257636592774293:ℚ)/462080000000000000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((3640625629:ℚ)/5000000000),((7496402281:ℚ)/10000000000),((-32634815967:ℚ)/110600000000),((-5801876887:ℚ)/28125000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2906445151:ℚ)/10000000000),((22699074775894305202840187590856216963150055516373313097:ℚ)/120794555000000000000000000000000000000000000000000000000),((28671839498056072663066717:ℚ)/462080000000000000000000000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((7401649157:ℚ)/10000000000),((3808374273:ℚ)/5000000000),((-16738619911:ℚ)/56250000000),((-11964947471:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2289677553:ℚ)/10000000000),((21000188743206663752490511218499426458358294823122259783:ℚ)/111236572265625000000000000000000000000000000000000000000),((100175912750906020068636013:ℚ)/1848320000000000000000000000)⟩
theorem valid11 : Valid source33 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((1880497803:ℚ)/2500000000),((2144451297:ℚ)/2500000000),((-773166083:ℚ)/2200000000),((-3081493409:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),((143400989:ℚ)/1000000000),((1102466486882733297100480212970544811559998174142457:ℚ)/4991250000000000000000000000000000000000000000000000),((5345501501776527284513933:ℚ)/115520000000000000000000000)⟩
theorem valid12 : Valid source33 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((530188673:ℚ)/625000000),((209870783:ℚ)/200000000),((-357431827:ℚ)/864000000),((-950566019:ℚ)/5000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((19067217435335433357763483253758946505199348934017:ℚ)/75582720000000000000000000000000000000000000000000),((263007:ℚ)/6400000)⟩
theorem valid13 : Valid source33 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((519935577:ℚ)/500000000),((14311916233:ℚ)/10000000000),((-80343413631:ℚ)/160000000000),((-1047806731:ℚ)/5520000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((4988348129639498668222682495639075743:ℚ)/16000000000000000000000000000000000000),((263007:ℚ)/6400000)⟩
theorem valid14 : Valid source33 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source33 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2079:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source33 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source33 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source33 nn0 nn1 Qcell ((2079:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source33 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source33 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source33 nn0 nn1 Qcell ((431:ℚ)/640) ((45:ℚ)/64) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source33 nn0 nn1 Qcell ((431:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC10
#check @N11Formalization.C450Source33GroupedC10.bound
#print axioms N11Formalization.C450Source33GroupedC10.valid0
#print axioms N11Formalization.C450Source33GroupedC10.valid1
#print axioms N11Formalization.C450Source33GroupedC10.valid2
#print axioms N11Formalization.C450Source33GroupedC10.valid3
#print axioms N11Formalization.C450Source33GroupedC10.valid4
#print axioms N11Formalization.C450Source33GroupedC10.valid5
#print axioms N11Formalization.C450Source33GroupedC10.valid6
#print axioms N11Formalization.C450Source33GroupedC10.valid7
#print axioms N11Formalization.C450Source33GroupedC10.valid8
#print axioms N11Formalization.C450Source33GroupedC10.valid9
#print axioms N11Formalization.C450Source33GroupedC10.valid10
#print axioms N11Formalization.C450Source33GroupedC10.valid11
#print axioms N11Formalization.C450Source33GroupedC10.valid12
#print axioms N11Formalization.C450Source33GroupedC10.valid13
#print axioms N11Formalization.C450Source33GroupedC10.valid14
#print axioms N11Formalization.C450Source33GroupedC10.bound
#print axioms N11Formalization.C450Source33GroupedC10.endpoint_checks
