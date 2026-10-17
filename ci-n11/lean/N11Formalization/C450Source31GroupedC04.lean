import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((1404468203:ℚ)/2000000000),((290196263:ℚ)/400000000),((-3030151419:ℚ)/3968000000),((-1084468203:ℚ)/1685000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((1962022307:ℚ)/5000000000),((14589313998865353059104648255809237:ℚ)/37076729468750000000000000000000000),((415381072412443884776962231:ℚ)/591462400000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((3570996713:ℚ)/5000000000),((365732269:ℚ)/500000000),((-1275506499:ℚ)/1685000000),((-8312990139:ℚ)/12756250000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((436173829:ℚ)/1250000000),((106092604108018021613165985050594492695242573259540430409:ℚ)/273249264562320709228515625000000000000000000000000000000),((2594169067795104238362152671:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((7201806889:ℚ)/10000000000),((3687188707:ℚ)/5000000000),((-38653453191:ℚ)/51025000000),((-16805420667:ℚ)/25750000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((406424391:ℚ)/1250000000),((3379655359009779486787092547420850614195703989769844181521:ℚ)/8711936746093750000000000000000000000000000000000000000000),((10378797710971382200939795039:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((7261612177:ℚ)/10000000000),((7434102863:ℚ)/10000000000),((-78083337219:ℚ)/103000000000),((-1887204059:ℚ)/2887500000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((74882493:ℚ)/250000000),((53212168518864251333010560354693598083119956788759:ℚ)/137279176712036132812500000000000000000000000000000),((10380833928906782437750991311:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((1464281903:ℚ)/2000000000),((749382191:ℚ)/1000000000),((-2628656161:ℚ)/3465000000),((-3432845709:ℚ)/5245000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((678995671:ℚ)/2500000000),((242058855332655843126119668206572990829728462238150317531:ℚ)/624956413872656250000000000000000000000000000000000000000),((415311398340298564002462031:ℚ)/591462400000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((1845299781:ℚ)/2500000000),((7613241487:ℚ)/10000000000),((-80412139331:ℚ)/104900000000),((-1445299781:ℚ)/2225000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((120268033:ℚ)/500000000),((28259493192674293485492530089083446291381482346252396503:ℚ)/72218015722656250000000000000000000000000000000000000000),((649640938882374233225827799:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((1875188997:ℚ)/2500000000),((122687673:ℚ)/156250000),((-1304939749:ℚ)/1668750000),((-4425566991:ℚ)/6912500000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1617834507:ℚ)/10000000000),((4487773992478919919094289843593169935657602051681862559:ℚ)/11248655895996093750000000000000000000000000000000000000),((648315645255438277613433431:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((7739785747:ℚ)/10000000000),((4045347841:ℚ)/5000000000),((-43309521933:ℚ)/55300000000),((-18419357241:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((32150131126147162962273320689383351306632707533786261815211:ℚ)/80854323550000000000000000000000000000000000000000000000000),((717118389:ℚ)/1024000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((7978712961:ℚ)/10000000000),((1130591891:ℚ)/1250000000),((-12377694583:ℚ)/14300000000),((-6378712961:ℚ)/10800000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((4589240592257627253324760047101177781381332343580826407:ℚ)/10424700000000000000000000000000000000000000000000000000),((717118389:ℚ)/1024000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((558348663:ℚ)/625000000),((10950501243:ℚ)/10000000000),((-123796516159:ℚ)/129600000000),((-1375045989:ℚ)/2500000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((237692276835719102752471276690523635203139277991836383:ℚ)/494384765625000000000000000000000000000000000000000000),((717118389:ℚ)/1024000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((10840521549:ℚ)/10000000000),((14757257619:ℚ)/10000000000),(-1:ℚ),((-9240521549:ℚ)/18400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((800038315102995716681937665734037149:ℚ)/1557376000000000000000000000000000000),((717118389:ℚ)/1024000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source31 nn0 nn1 Qcell ((2041:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source31 nn0 nn1 Qcell ((1049:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source31 nn0 nn1 Qcell ((1049:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC04
#check @N11Formalization.C450Source31GroupedC04.bound
#print axioms N11Formalization.C450Source31GroupedC04.valid0
#print axioms N11Formalization.C450Source31GroupedC04.valid1
#print axioms N11Formalization.C450Source31GroupedC04.valid2
#print axioms N11Formalization.C450Source31GroupedC04.valid3
#print axioms N11Formalization.C450Source31GroupedC04.valid4
#print axioms N11Formalization.C450Source31GroupedC04.valid5
#print axioms N11Formalization.C450Source31GroupedC04.valid6
#print axioms N11Formalization.C450Source31GroupedC04.valid7
#print axioms N11Formalization.C450Source31GroupedC04.valid8
#print axioms N11Formalization.C450Source31GroupedC04.valid9
#print axioms N11Formalization.C450Source31GroupedC04.valid10
#print axioms N11Formalization.C450Source31GroupedC04.bound
#print axioms N11Formalization.C450Source31GroupedC04.endpoint_checks
