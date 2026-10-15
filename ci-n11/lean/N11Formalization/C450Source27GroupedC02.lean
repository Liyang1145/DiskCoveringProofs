import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((2003:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7056069889:ℚ)/10000000000),((3611951969:ℚ)/5000000000),((-9235855907:ℚ)/9920000000),((-41072489223:ℚ)/50075000000),((398569427:ℚ)/400000000),(1:ℚ),((845998389:ℚ)/10000000000),((951578519:ℚ)/2500000000),((42938008379913189805240285830711552394414051:ℚ)/122390282361856000000000000000000000000000000),((717908441290679980832301347:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((2003:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((2003:ℚ)/3200),((1011:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((3557812499:ℚ)/5000000000),((7283377493:ℚ)/10000000000),((-18650132479:ℚ)/20030000000),((-6914895831:ℚ)/8425000000),((9929701407:ℚ)/10000000000),((62276473:ℚ)/62500000),((18538009:ℚ)/156250000),((897373211:ℚ)/2500000000),((78104468734651204793808313983037629670614510729248571033:ℚ)/222814116160244873046875000000000000000000000000000000000),((2880579780870238981575926923:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((2003:ℚ)/3200) ((1011:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1011:ℚ)/1600),((4063:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((3587588353:ℚ)/5000000000),((3656556789:ℚ)/5000000000),((-9369670367:ℚ)/10110000000),((-20953118471:ℚ)/25393750000),((4956442379:ℚ)/5000000000),((2482425353:ℚ)/2500000000),((1320924081:ℚ)/10000000000),((3359359089:ℚ)/10000000000),((15004471565323611075657435838418176725952363974474461633377:ℚ)/43552763331938671875000000000000000000000000000000000000000),((721264563450875844013531467:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4063:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4063:ℚ)/6400),((2041:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((1801237829:ℚ)/2500000000),((7342849209:ℚ)/10000000000),((-18828547627:ℚ)/20315000000),((-10528664803:ℚ)/12756250000),((247409071:ℚ)/250000000),((9912884763:ℚ)/10000000000),((1440948769:ℚ)/10000000000),((3238418133:ℚ)/10000000000),((444845788159755324841348056378714444027853158350125920620981:ℚ)/1291605251547267968750000000000000000000000000000000000000000),((2889540371048625496196684787:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((4063:ℚ)/6400) ((2041:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7234725111:ℚ)/10000000000),((7372584393:ℚ)/10000000000),((-1455211783:ℚ)/1570000000),((-42323075777:ℚ)/51262500000),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((124518269:ℚ)/400000000),((1867469415785219266030045254127681235290088195593605034643:ℚ)/5423719860207750000000000000000000000000000000000000000000),((2894026133491988460729648723:ℚ)/2957312000000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4101:ℚ)/6400),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((7264498103:ℚ)/10000000000),((231322473:ℚ)/312500000),((-593967419:ℚ)/640781250),((-42531486721:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((9880131563:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((745600947:ℚ)/2500000000),((42702762578426360305764074255898691104216992149198392593:ℚ)/124057012154695129394531250000000000000000000000000000000),((7840946215678100914203:ℚ)/8000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((4101:ℚ)/6400) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7294270303:ℚ)/10000000000),((1486410689:ℚ)/2000000000),((-3819232067:ℚ)/4120000000),((-42739892121:ℚ)/51737500000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((711514519:ℚ)/2500000000),((10065547836356578439440371259495375828369293912741412872741:ℚ)/29249776566198437500000000000000000000000000000000000000000),((116120343883318157404544867:ℚ)/118292480000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((3662020861:ℚ)/5000000000),((298471493:ℚ)/400000000),((-767414479:ℚ)/827800000),((-21474146027:ℚ)/25987500000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((540608489:ℚ)/2000000000),((478171299541974680644747810136693454758961466596588553:ℚ)/1389909950407638000000000000000000000000000000000000000),((4652008479547963573994923:ℚ)/4731699200000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((7353812371:ℚ)/10000000000),((7521253821:ℚ)/10000000000),((-19363761463:ℚ)/20790000000),((-43156686597:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((2552235151:ℚ)/10000000000),((10387942154376482439885557548441684433003684642975743284799:ℚ)/29726239491506250000000000000000000000000000000000000000000),((2916509650101309836917776507:ℚ)/2957312000000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((37066757:ℚ)/50000000),((47751137:ℚ)/62500000),((-123253411:ℚ)/131125000),((-72622433:ℚ)/89000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((222082031:ℚ)/1000000000),((40190344626094442221528929774370003444213398389070997:ℚ)/111613450448352050781250000000000000000000000000000000),((202801673:ℚ)/204800000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((7532420669:ℚ)/10000000000),((3939009861:ℚ)/5000000000),((-10217029583:ℚ)/10680000000),((-44406944683:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1334558099:ℚ)/10000000000),((6027501666644547497355071106663475592490691293751427026387:ℚ)/15838961504400000000000000000000000000000000000000000000000),((202801673:ℚ)/204800000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((3885263087:ℚ)/5000000000),((4057917519:ℚ)/5000000000),((-10573752557:ℚ)/11060000000),((-23036841609:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((9341294411068960161662226607479553439135011574465017577677:ℚ)/24701278551950000000000000000000000000000000000000000000000),((202801673:ℚ)/204800000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((8008591309:ℚ)/10000000000),((9066911087:ℚ)/10000000000),(-1:ℚ),((-5304459907:ℚ)/7200000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((115496205840317153072946726464848021:ℚ)/259200000000000000000000000000000000),((202801673:ℚ)/204800000)⟩
theorem valid12 : Valid source27 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((8960519461:ℚ)/10000000000),((10968449107:ℚ)/10000000000),(-1:ℚ),((-54403636227:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3700746612731715020433600909414429609:ℚ)/8000000000000000000000000000000000000),((202801673:ℚ)/204800000)⟩
theorem valid13 : Valid source27 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((10863274373:ℚ)/10000000000),((2954050743:ℚ)/2000000000),(-1:ℚ),((-67722920611:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((3041026274786697353542331971:ℚ)/6094080000000000000000000000),((202801673:ℚ)/204800000)⟩
theorem valid14 : Valid source27 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source27 nn0 nn1 Qcell ((2003:ℚ)/3200) ((4063:ℚ)/6400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((4063:ℚ)/6400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source27 nn0 nn1 Qcell ((4063:ℚ)/6400) ((4101:ℚ)/6400) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source27 nn0 nn1 Qcell ((4101:ℚ)/6400) ((4139:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source27 nn0 nn1 Qcell ((4063:ℚ)/6400) ((4139:ℚ)/6400) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((4139:ℚ)/6400) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source27 nn0 nn1 Qcell ((4139:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source27 nn0 nn1 Qcell ((1049:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source27 nn0 nn1 Qcell ((4139:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source27 nn0 nn1 Qcell ((4139:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC02
#check @N11Formalization.C450Source27GroupedC02.bound
#print axioms N11Formalization.C450Source27GroupedC02.valid0
#print axioms N11Formalization.C450Source27GroupedC02.valid1
#print axioms N11Formalization.C450Source27GroupedC02.valid2
#print axioms N11Formalization.C450Source27GroupedC02.valid3
#print axioms N11Formalization.C450Source27GroupedC02.valid4
#print axioms N11Formalization.C450Source27GroupedC02.valid5
#print axioms N11Formalization.C450Source27GroupedC02.valid6
#print axioms N11Formalization.C450Source27GroupedC02.valid7
#print axioms N11Formalization.C450Source27GroupedC02.valid8
#print axioms N11Formalization.C450Source27GroupedC02.valid9
#print axioms N11Formalization.C450Source27GroupedC02.valid10
#print axioms N11Formalization.C450Source27GroupedC02.valid11
#print axioms N11Formalization.C450Source27GroupedC02.valid12
#print axioms N11Formalization.C450Source27GroupedC02.valid13
#print axioms N11Formalization.C450Source27GroupedC02.valid14
#print axioms N11Formalization.C450Source27GroupedC02.bound
#print axioms N11Formalization.C450Source27GroupedC02.endpoint_checks
