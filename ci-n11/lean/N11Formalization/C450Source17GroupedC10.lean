import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((3199999999:ℚ)/5000000000),((6691724127:ℚ)/10000000000),((-37242068889:ℚ)/99200000000),((-7039999997:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2848106599:ℚ)/5000000000),((324316176901764354156201033368438660409274357943048921537:ℚ)/4962090380859375000000000000000000000000000000000000000000),((55000188584338413449740767:ℚ)/462080000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((6638425857:ℚ)/10000000000),((3405471409:ℚ)/5000000000),((-19038299863:ℚ)/51500000000),((-14795277571:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5084973403:ℚ)/10000000000),((738227795962355157936433924949983789584479106902656399621:ℚ)/11610842465527343750000000000000000000000000000000000000000),((213148720660676521246732383:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((1689403373:ℚ)/2500000000),((3465072369:ℚ)/5000000000),((-19455506583:ℚ)/52450000000),((-3788210119:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((118822711:ℚ)/250000000),((123769891575475635384759824283018535737506631948326197343:ℚ)/1949886424511718750000000000000000000000000000000000000000),((36307545262455498943263:ℚ)/320000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((107449773:ℚ)/156250000),((1762332693:ℚ)/2500000000),((-3312109617:ℚ)/8900000000),((-242349319:ℚ)/849218750),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1099480267:ℚ)/2500000000),((5397566592203477967770485444707588566582181116112849:ℚ)/85166491394490003585815429687500000000000000000000000),((50358674279390828820243:ℚ)/451250000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((55967541:ℚ)/80000000),((7108918091:ℚ)/10000000000),((-40162426637:ℚ)/108700000000),((-126942623:ℚ)/438600000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4013901191:ℚ)/10000000000),((1495058685462910260594242300649429137879133518670659:ℚ)/23883842672831250000000000000000000000000000000000000),((12980412467172231924327:ℚ)/118292480000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((7055515883:ℚ)/10000000000),((1433700349:ℚ)/2000000000),((-8115902443:ℚ)/21930000000),((-16046547649:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1904137877:ℚ)/5000000000),((1132908990012120566643617322227749817883868544196392283809:ℚ)/18108566541064453125000000000000000000000000000000000000000),((201091246074786264842711463:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((7115085719:ℚ)/10000000000),((289123273:ℚ)/400000000),((-1639862911:ℚ)/4424000000),((-16225257157:ℚ)/55775000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3591512217:ℚ)/10000000000),((12080306516627124527051395409308745245017878368779309149:ℚ)/193197798336791992187500000000000000000000000000000000000),((199361806728938436802059087:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((358732611:ℚ)/500000000),((291506337:ℚ)/400000000),((-1656544359:ℚ)/4462000000),((-820197833:ℚ)/2812500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((840362979:ℚ)/2500000000),((113594346152393943424233699194262579976119166247417533:ℚ)/1817642524838447570800781250000000000000000000000000000),((494076561373153892445207:ℚ)/4620800000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((452138467:ℚ)/625000000),((7347231631:ℚ)/10000000000),((-41830621417:ℚ)/112500000000),((-1036415401:ℚ)/3545312500),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((77878633:ℚ)/250000000),((21746113358306319173803715179273403396348085739357:ℚ)/348139736324548721313476562500000000000000000000000),((765225380239605164548263:ℚ)/7220000000000000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((1823443889:ℚ)/2500000000),((7406801529:ℚ)/10000000000),((-42247610703:ℚ)/113450000000),((-4190331667:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1424187823:ℚ)/5000000000),((1294516449250638227801807449706985371910402148098288034431:ℚ)/20734455259375000000000000000000000000000000000000000000000),((33615481829261594374887:ℚ)/320000000000000000000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((7353332551:ℚ)/10000000000),((7525931727:ℚ)/10000000000),((-43081522089:ℚ)/114400000000),((-16939997653:ℚ)/58150000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1277367349:ℚ)/5000000000),((426088955014166266709354262311750744849683149066312033999:ℚ)/6759146569140625000000000000000000000000000000000000000000),((192426599651655369184289967:ℚ)/1848320000000000000000000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((7472437583:ℚ)/10000000000),((3822524823:ℚ)/5000000000),((-21957673761:ℚ)/58150000000),((-17297312749:ℚ)/59100000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((917379237:ℚ)/5000000000),((437401030166810872712501391894427190251591713807167499053:ℚ)/6946538124218750000000000000000000000000000000000000000000),((188948497679059941495268863:ℚ)/1848320000000000000000000000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/16),((-3:ℚ)/8),((474470697:ℚ)/625000000),((985406369:ℚ)/1250000000),((-5697844583:ℚ)/14775000000),((-1103412091:ℚ)/3812500000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((118032259:ℚ)/2500000000),((6558836544182284664350592753382374846938192152453772373:ℚ)/102345101165771484375000000000000000000000000000000000000),((724466314637831406085503:ℚ)/7220000000000000000000000)⟩
theorem valid12 : Valid source17 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((7829686053:ℚ)/10000000000),((2089882423:ℚ)/2500000000),((-12229176961:ℚ)/30500000000),((-18369058159:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1142735716167850189315933437701062828826634359540000608249:ℚ)/17289547200000000000000000000000000000000000000000000000000),((6413271:ℚ)/64000000)⟩
theorem valid13 : Valid source17 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((8305880209:ℚ)/10000000000),((2565856567:ℚ)/2500000000),((-15560995969:ℚ)/32400000000),((-19797640627:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((122111620293870449670878045017975463625725434464371412299:ℚ)/1600000000000000000000000000000000000000000000000000000000),((6413271:ℚ)/64000000)⟩
theorem valid14 : Valid source17 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((2041903853:ℚ)/2000000000),((14067994781:ℚ)/10000000000),((-88875963467:ℚ)/160000000000),((-5101711559:ℚ)/22080000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2211315352507832990452723696907402882141699198671094141:ℚ)/25229491200000000000000000000000000000000000000000000000),((6413271:ℚ)/64000000)⟩
theorem valid15 : Valid source17 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source17 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC10
#check @N11Formalization.C450Source17GroupedC10.bound
#print axioms N11Formalization.C450Source17GroupedC10.valid0
#print axioms N11Formalization.C450Source17GroupedC10.valid1
#print axioms N11Formalization.C450Source17GroupedC10.valid2
#print axioms N11Formalization.C450Source17GroupedC10.valid3
#print axioms N11Formalization.C450Source17GroupedC10.valid4
#print axioms N11Formalization.C450Source17GroupedC10.valid5
#print axioms N11Formalization.C450Source17GroupedC10.valid6
#print axioms N11Formalization.C450Source17GroupedC10.valid7
#print axioms N11Formalization.C450Source17GroupedC10.valid8
#print axioms N11Formalization.C450Source17GroupedC10.valid9
#print axioms N11Formalization.C450Source17GroupedC10.valid10
#print axioms N11Formalization.C450Source17GroupedC10.valid11
#print axioms N11Formalization.C450Source17GroupedC10.valid12
#print axioms N11Formalization.C450Source17GroupedC10.valid13
#print axioms N11Formalization.C450Source17GroupedC10.valid14
#print axioms N11Formalization.C450Source17GroupedC10.valid15
#print axioms N11Formalization.C450Source17GroupedC10.bound
#print axioms N11Formalization.C450Source17GroupedC10.endpoint_checks
