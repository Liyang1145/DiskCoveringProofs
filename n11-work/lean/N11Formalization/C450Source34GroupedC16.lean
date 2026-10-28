import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC16
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((-1:ℚ)/16),(0:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/16),(0:ℚ),((6057854403:ℚ)/10000000000),((1597367393:ℚ)/2500000000),((3522632607:ℚ)/25750000000),((33:ℚ)/155),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3241709979:ℚ)/5000000000),((-12369390199933591537276190943304542235881991680060387710391:ℚ)/102549867871093750000000000000000000000000000000000000000000),((-191914854895998677:ℚ)/972800000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((6300714739:ℚ)/10000000000),((6510584273:ℚ)/10000000000),((13969415727:ℚ)/104900000000),((528:ℚ)/2575),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((296702539:ℚ)/500000000),((-2247069549108932245945999721011730087503130494945177597342911:ℚ)/19134668383189062500000000000000000000000000000000000000000000),((-201618669668075301:ℚ)/972800000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/16),(0:ℚ),((802749319:ℚ)/1250000000),((6631612399:ℚ)/10000000000),((13848387601:ℚ)/106800000000),((1056:ℚ)/5245),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((1128465001:ℚ)/2000000000),((-239494558781792691242001601325581731589860443111732862514169177:ℚ)/2094521199936300000000000000000000000000000000000000000000000000),((-25808071176969521:ℚ)/121600000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((6543181563:ℚ)/10000000000),((3376279331:ℚ)/5000000000),((6863720669:ℚ)/54350000000),((88:ℚ)/445),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2668359971:ℚ)/5000000000),((-885452127749157119688975228347791341855031240059625194899653:ℚ)/7948014960361718750000000000000000000000000000000000000000000),((-11121408480705743:ℚ)/51200000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/16),(0:ℚ),((3332140417:ℚ)/5000000000),((6813002473:ℚ)/10000000000),((803941031:ℚ)/6450000000),((1056:ℚ)/5435),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((626831783:ℚ)/1250000000),((-18167834116771785577097644001230070203263490267676256564541:ℚ)/165134191083398437500000000000000000000000000000000000000000),((-108072723540061703:ℚ)/486400000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((840599881:ℚ)/1250000000),((6873427433:ℚ)/10000000000),((1943796081:ℚ)/15800000000),((704:ℚ)/3655),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((151450501:ℚ)/312500000),((-22360698626678892116689155765301283804503309548728086180113:ℚ)/205828760217968750000000000000000000000000000000000000000000),((-1437917990557541:ℚ)/6400000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/16),(0:ℚ),((3392648531:ℚ)/5000000000),((874277847:ℚ)/1250000000),((1685722153:ℚ)/14062500000),((528:ℚ)/2765),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4672679997:ℚ)/10000000000),((-83534193111068141206900835759454639404141922295556878637:ℚ)/788446236401796340942382812500000000000000000000000000000),((-5815284603445191:ℚ)/25600000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/16),(0:ℚ),((6906234613:ℚ)/10000000000),((3557474237:ℚ)/5000000000),((6682525763:ℚ)/57200000000),((352:ℚ)/1875),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((538251147:ℚ)/1250000000),((-362869488560037888664255421708160798683354391221274454057:ℚ)/3509048400000000000000000000000000000000000000000000000000),((-225813039135254067:ℚ)/972800000000000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((7027097549:ℚ)/10000000000),((1149407:ℚ)/1562500),((683531:ℚ)/6156250),((12:ℚ)/65),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1953822987:ℚ)/5000000000),((-15422727593800822069730526648745490184576217:ℚ)/156372094154357910156250000000000000000000000),((-230642281995864091:ℚ)/972800000000000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/16),(0:ℚ),((7268614463:ℚ)/10000000000),((949652737:ℚ)/1250000000),((1610347263:ℚ)/15250000000),((176:ℚ)/985),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((592783081:ℚ)/2000000000),((-81124773508762777370654644595121568295633768478610273315911:ℚ)/860244690332031250000000000000000000000000000000000000000000),((-240292418516220217:ℚ)/972800000000000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/16),(0:ℚ),((7509875163:ℚ)/10000000000),((2019656221:ℚ)/2500000000),((3100343779:ℚ)/32400000000),((264:ℚ)/1525),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1541560449:ℚ)/10000000000),((-22837988218505626201262390616814105437238473539584200350801:ℚ)/263665594800000000000000000000000000000000000000000000000000),((-249932317658011517:ℚ)/972800000000000000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/16),(0:ℚ),((7991720713:ℚ)/10000000000),((999806433:ℚ)/1000000000),((1048193567:ℚ)/16000000000),((22:ℚ)/135),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-134789858860133899282985472050206328984995601167733640791:ℚ)/2073600000000000000000000000000000000000000000000000000000),((-6671931:ℚ)/25600000)⟩
theorem valid11 : Valid source34 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/16),(0:ℚ),((247812429:ℚ)/250000000),((13820742341:ℚ)/10000000000),((2219752553:ℚ)/73600000000),((33:ℚ)/250),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-76012914311792029943679298504677066152454883990926795067:ℚ)/1868851200000000000000000000000000000000000000000000000000),((-6671931:ℚ)/25600000)⟩
theorem valid12 : Valid source34 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC16
#check @N11Formalization.C450Source34GroupedC16.bound
#print axioms N11Formalization.C450Source34GroupedC16.valid0
#print axioms N11Formalization.C450Source34GroupedC16.valid1
#print axioms N11Formalization.C450Source34GroupedC16.valid2
#print axioms N11Formalization.C450Source34GroupedC16.valid3
#print axioms N11Formalization.C450Source34GroupedC16.valid4
#print axioms N11Formalization.C450Source34GroupedC16.valid5
#print axioms N11Formalization.C450Source34GroupedC16.valid6
#print axioms N11Formalization.C450Source34GroupedC16.valid7
#print axioms N11Formalization.C450Source34GroupedC16.valid8
#print axioms N11Formalization.C450Source34GroupedC16.valid9
#print axioms N11Formalization.C450Source34GroupedC16.valid10
#print axioms N11Formalization.C450Source34GroupedC16.valid11
#print axioms N11Formalization.C450Source34GroupedC16.valid12
#print axioms N11Formalization.C450Source34GroupedC16.bound
#print axioms N11Formalization.C450Source34GroupedC16.endpoint_checks
