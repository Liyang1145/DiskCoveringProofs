import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((6916421721:ℚ)/10000000000),((7141993431:ℚ)/10000000000),((-16945980293:ℚ)/24800000000),((-57520638931:ℚ)/101100000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4273784093:ℚ)/10000000000),((10078742929190803268028681488161227187:ℚ)/28704564750000000000000000000000000000),((25687200542334449592279453:ℚ)/46208000000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7036187161:ℚ)/10000000000),((3600903447:ℚ)/5000000000),((-8562710341:ℚ)/12637500000),((-58838058771:ℚ)/102050000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((1938062801:ℚ)/5000000000),((145566705529427133954960328486303354047404421383399428634219:ℚ)/419710870367724609375000000000000000000000000000000000000000),((25586773924361317054392093:ℚ)/46208000000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((7096055523:ℚ)/10000000000),((3630806091:ℚ)/5000000000),((-8652418273:ℚ)/12756250000),((-59496610753:ℚ)/103000000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((3662090301:ℚ)/10000000000),((193253194949475263989146729483440033632815044463056467098467:ℚ)/557563951750000000000000000000000000000000000000000000000000),((25543488140651143815956757:ℚ)/46208000000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((3577957337:ℚ)/5000000000),((91517619:ℚ)/125000000),((-218552857:ℚ)/321875000),((-1432263367:ℚ)/2475000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((1717707369:ℚ)/5000000000),((489109754581527896039400712789691059759374413607217:ℚ)/1412014389038085937500000000000000000000000000000000),((6374928228827172822610077:ℚ)/11552000000000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((1803941217:ℚ)/2500000000),((7381199129:ℚ)/10000000000),((-17663597387:ℚ)/25987500000),((-15203353387:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((1596701267:ℚ)/5000000000),((81133071583066367258700372020499524064814299002196159940063:ℚ)/234358655202246093750000000000000000000000000000000000000000),((1590965517511577905088237:ℚ)/2888000000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((3637803177:ℚ)/5000000000),((3720490609:ℚ)/5000000000),((-8921471827:ℚ)/13112500000),((-30735834947:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((2932252511:ℚ)/10000000000),((336293710320679985090882432751966208116114432230157945727817:ℚ)/971936978323925781250000000000000000000000000000000000000000),((6352673565159984524980157:ℚ)/11552000000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((7335439369:ℚ)/10000000000),((7500755993:ℚ)/10000000000),((-18022267979:ℚ)/26462500000),((-20709944353:ℚ)/35600000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((2646298113:ℚ)/10000000000),((51611768979226137060446055223514506558910261960548165394311:ℚ)/149241937300000000000000000000000000000000000000000000000000),((25365450885168887950342013:ℚ)/46208000000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((7395264143:ℚ)/10000000000),((1905071093:ℚ)/2500000000),((-4595213279:ℚ)/6675000000),((-62787905573:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2326403063:ℚ)/10000000000),((748455523133357923877212417246024676292628716846029945057941:ℚ)/2143284933131250000000000000000000000000000000000000000000000),((25329830121836988825991117:ℚ)/46208000000000000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((3757444923:ℚ)/5000000000),((967473219:ℚ)/1250000000),((-2342419657:ℚ)/3396875000),((-32051894153:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((187247071:ℚ)/1250000000),((25049514561461618331746178072304297977873085881977683283269:ℚ)/71806700702734375000000000000000000000000000000000000000000),((6301570723135601107825957:ℚ)/11552000000000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((3817242569:ℚ)/5000000000),((3989356483:ℚ)/5000000000),((-1389724207:ℚ)/1975000000),((-32709668259:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((32832565234033464929398658457976140638192685176191509472351:ℚ)/92404941200000000000000000000000000000000000000000000000000),((8697083:ℚ)/16000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((7873590639:ℚ)/10000000000),((8933578613:ℚ)/10000000000),((-22320735839:ℚ)/28600000000),((-68049497029:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((7067148110179338297324164537352228660683892066062005359379:ℚ)/18013881600000000000000000000000000000000000000000000000000),((8697083:ℚ)/16000000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((4414531609:ℚ)/5000000000),((5420260777:ℚ)/5000000000),((-14020782331:ℚ)/16200000000),((-39279847699:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((277962349080347839937702852651043653891:ℚ)/648000000000000000000000000000000000000),((8697083:ℚ)/16000000)⟩
theorem valid11 : Valid source30 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((5368435059:ℚ)/5000000000),((14648653783:ℚ)/10000000000),((-39465961349:ℚ)/40000000000),((-49772785649:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1001427773931880815660734147:ℚ)/2031360000000000000000000000),((8697083:ℚ)/16000000)⟩
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
end N11Formalization.C450Source30GroupedC05
#check @N11Formalization.C450Source30GroupedC05.bound
#print axioms N11Formalization.C450Source30GroupedC05.valid0
#print axioms N11Formalization.C450Source30GroupedC05.valid1
#print axioms N11Formalization.C450Source30GroupedC05.valid2
#print axioms N11Formalization.C450Source30GroupedC05.valid3
#print axioms N11Formalization.C450Source30GroupedC05.valid4
#print axioms N11Formalization.C450Source30GroupedC05.valid5
#print axioms N11Formalization.C450Source30GroupedC05.valid6
#print axioms N11Formalization.C450Source30GroupedC05.valid7
#print axioms N11Formalization.C450Source30GroupedC05.valid8
#print axioms N11Formalization.C450Source30GroupedC05.valid9
#print axioms N11Formalization.C450Source30GroupedC05.valid10
#print axioms N11Formalization.C450Source30GroupedC05.valid11
#print axioms N11Formalization.C450Source30GroupedC05.valid12
#print axioms N11Formalization.C450Source30GroupedC05.bound
#print axioms N11Formalization.C450Source30GroupedC05.endpoint_checks
