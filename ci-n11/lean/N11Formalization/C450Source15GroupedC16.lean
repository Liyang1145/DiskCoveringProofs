import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC16
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((-1:ℚ)/16),(0:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/16),(0:ℚ),((6174657883:ℚ)/10000000000),((6687293857:ℚ)/10000000000),((544235381:ℚ)/35600000000),((14:ℚ)/155),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((778057129:ℚ)/1250000000),((878449669705292054624841848559:ℚ)/18877960880000000000000000000000),((-15117403929306789:ℚ)/194560000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((6651467881:ℚ)/10000000000),((6806398091:ℚ)/10000000000),((1513601909:ℚ)/108700000000),((112:ℚ)/1335),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5049614137:ℚ)/10000000000),((16865168040419265794186317270753722532253503:ℚ)/374836282362450000000000000000000000000000000),((-16675420173001623:ℚ)/194560000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((6770630623:ℚ)/10000000000),((6925490101:ℚ)/10000000000),((1394509899:ℚ)/110600000000),((448:ℚ)/5435),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4715341357:ℚ)/10000000000),((878857610345032856845780096518690599501978187:ℚ)/19638526505346350000000000000000000000000000000),((-17064794322994209:ℚ)/194560000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/16),(0:ℚ),((861222389:ℚ)/1250000000),((7044570511:ℚ)/10000000000),((425143163:ℚ)/37500000000),((32:ℚ)/395),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4357591127:ℚ)/10000000000),((154373867517048878565571319217177428674051:ℚ)/3466680468750000000000000000000000000000000),((-2181765237515787:ℚ)/24320000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/16),(0:ℚ),((1752228519:ℚ)/2500000000),((1776026637:ℚ)/2500000000),((303973363:ℚ)/28362500000),((448:ℚ)/5625),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((3969988783:ℚ)/10000000000),((225427122848898854580069788257625429225389:ℚ)/5090542492675781250000000000000000000000000),((-4460851320799577:ℚ)/48640000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/16),(0:ℚ),((70684767:ℚ)/100000000),((7163639901:ℚ)/10000000000),((1156360099:ℚ)/114400000000),((896:ℚ)/11345),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3762127967:ℚ)/10000000000),((6755926386610343452082711433021305828866542249:ℚ)/152881711710682240000000000000000000000000000000),((-180380311008161:ℚ)/1945600000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/16),(0:ℚ),((7128036193:ℚ)/10000000000),((1444634127:ℚ)/2000000000),((219365873:ℚ)/23070000000),((56:ℚ)/715),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((442839233:ℚ)/1250000000),((19065978350353018858430098922863484519799:ℚ)/432315493931750000000000000000000000000000),((-18232646687631519:ℚ)/194560000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((7187592633:ℚ)/10000000000),((3641349407:ℚ)/5000000000),((518650593:ℚ)/58150000000),((896:ℚ)/11535),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3309444701:ℚ)/10000000000),((67687160912116496984863423213563464373182553:ℚ)/1537724229696302500000000000000000000000000000),((-18427252298516039:ℚ)/194560000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((1449429219:ℚ)/2000000000),((7401747759:ℚ)/10000000000),((918252241:ℚ)/118200000000),((448:ℚ)/5815),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3059147693:ℚ)/10000000000),((805472852130243071188942038717556210307200889:ℚ)/18314406576996900000000000000000000000000000000),((-3724369635707677:ℚ)/38912000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((920780547:ℚ)/1250000000),((7520787211:ℚ)/10000000000),((799212789:ℚ)/120100000000),((224:ℚ)/2955),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((248661593:ℚ)/1000000000),((217508216782385461656522977795572425250966031:ℚ)/4962462147257850000000000000000000000000000000),((-2376376462107901:ℚ)/24320000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-1:ℚ)/16),(0:ℚ),((7485331591:ℚ)/10000000000),((1527963523:ℚ)/2000000000),((136036477:ℚ)/24400000000),((448:ℚ)/6005),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((869656341:ℚ)/5000000000),((225333235971304641679120845632099099496135547:ℚ)/5156780895456800000000000000000000000000000000),((-19400139056114553:ℚ)/194560000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/16),(0:ℚ),((7604408259:ℚ)/10000000000),((4057928373:ℚ)/5000000000),((102071627:ℚ)/64800000000),((112:ℚ)/1525),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((20870539137054026132288669549383907659471:ℚ)/476551149120000000000000000000000000000000),((-2601951:ℚ)/25600000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/16),(0:ℚ),((4040309393:ℚ)/5000000000),((2504842259:ℚ)/2500000000),((-424842259:ℚ)/32400000000),((28:ℚ)/405),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((382645524601963093600815216049:ℚ)/8649755859375000000000000000000),((-2601951:ℚ)/25600000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/16),(0:ℚ),((1996861537:ℚ)/2000000000),((13823677423:ℚ)/10000000000),((-5503677423:ℚ)/160000000000),((7:ℚ)/125),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((973265469412127:ℚ)/20000000000000000),((-2601951:ℚ)/25600000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((2307:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source15 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source15 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC16
#check @N11Formalization.C450Source15GroupedC16.bound
#print axioms N11Formalization.C450Source15GroupedC16.valid0
#print axioms N11Formalization.C450Source15GroupedC16.valid1
#print axioms N11Formalization.C450Source15GroupedC16.valid2
#print axioms N11Formalization.C450Source15GroupedC16.valid3
#print axioms N11Formalization.C450Source15GroupedC16.valid4
#print axioms N11Formalization.C450Source15GroupedC16.valid5
#print axioms N11Formalization.C450Source15GroupedC16.valid6
#print axioms N11Formalization.C450Source15GroupedC16.valid7
#print axioms N11Formalization.C450Source15GroupedC16.valid8
#print axioms N11Formalization.C450Source15GroupedC16.valid9
#print axioms N11Formalization.C450Source15GroupedC16.valid10
#print axioms N11Formalization.C450Source15GroupedC16.valid11
#print axioms N11Formalization.C450Source15GroupedC16.valid12
#print axioms N11Formalization.C450Source15GroupedC16.valid13
#print axioms N11Formalization.C450Source15GroupedC16.bound
#print axioms N11Formalization.C450Source15GroupedC16.endpoint_checks
