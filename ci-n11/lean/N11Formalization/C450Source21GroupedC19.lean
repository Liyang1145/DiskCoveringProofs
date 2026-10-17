import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((2999999999:ℚ)/5000000000),((817159171:ℚ)/1250000000),((2013333333:ℚ)/8900000000),((130692823:ℚ)/400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1321690593:ℚ)/2000000000),((10925770218700100008329073740582971:ℚ)/126736000000000000000000000000000000),((-63257292712292813583069583:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((3239291967:ℚ)/5000000000),((847031293:ℚ)/1250000000),((6279291967:ℚ)/27650000000),((4141093879:ℚ)/13350000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1100303271:ℚ)/2000000000),((52266807948843907410005483883418084058935562345984486178127:ℚ)/649644905453906250000000000000000000000000000000000000000000),((-66862102410988433122419087:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((1679422323:ℚ)/2500000000),((6895701081:ℚ)/10000000000),((3199422323:ℚ)/14062500000),((33487103243:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4866457571:ℚ)/10000000000),((7643670947735937891253543582352738045965093906337533682771:ℚ)/97843589550000000000000000000000000000000000000000000000000),((-4394248507676500337383600743:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((1709300227:ℚ)/2500000000),((3507564171:ℚ)/5000000000),((3229300227:ℚ)/14300000000),((16922692513:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2259355091:ℚ)/5000000000),((588621397980771964527888707148476310251394925138530546948461:ℚ)/7582255554199218750000000000000000000000000000000000000000000),((-1112019789611919261668199583:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((6956686989:ℚ)/10000000000),((7134533291:ℚ)/10000000000),((13036686989:ℚ)/58150000000),((34203599873:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((129503507:ℚ)/312500000),((244249982282374946372055793694150171751310064769714154494649527:ℚ)/3164153390226400000000000000000000000000000000000000000000000000),((-4501773703466280010874382303:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((7076148803:ℚ)/10000000000),((1450783403:ℚ)/2000000000),((13156148803:ℚ)/59100000000),((6912350209:ℚ)/23260000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((746911049:ℚ)/2000000000),((175824318997466295486149980342009546194213448808409102055573:ℚ)/2289300822124612500000000000000000000000000000000000000000000),((-182213311668050649280102367:ℚ)/591462400000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((3597793767:ℚ)/5000000000),((1843320133:ℚ)/2500000000),((6637793767:ℚ)/30025000000),((8729960399:ℚ)/29550000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1638458153:ℚ)/5000000000),((17785337374371197087824908695033221587946714240887217673583641:ℚ)/232615413152711718750000000000000000000000000000000000000000000),((-288047314318112513875643007:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((57148471:ℚ)/78125000),((1873156199:ℚ)/2500000000),((104648471:ℚ)/476562500),((8819468597:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2747223183:ℚ)/10000000000),((47939953217242658542163725985927423550487099783880762088307:ℚ)/629489855402441406250000000000000000000000000000000000000000),((-291377936352374066411916263:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((3717200053:ℚ)/5000000000),((7969826411:ℚ)/10000000000),((6757200053:ℚ)/32400000000),((36709479233:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1045682861:ℚ)/5000000000),((1465041697436680432437486746463746165303252010543724285628063:ℚ)/18615279262500000000000000000000000000000000000000000000000000),((-9695716001012813:ℚ)/30400000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((3955896301:ℚ)/5000000000),((1234566341:ℚ)/1250000000),((6995896301:ℚ)/40000000000),((5303699023:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((143263609002576462971154630685190336129940782202118297:ℚ)/1660753125000000000000000000000000000000000000000000000),((-332453509:ℚ)/1024000000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((4909538593:ℚ)/5000000000),((684219203:ℚ)/500000000),((7949538593:ℚ)/55200000000),((2692657609:ℚ)/8000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((64248041172640545175791679882814398957:ℚ)/609408000000000000000000000000000000000),((-332453509:ℚ)/1024000000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source21 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC19
#check @N11Formalization.C450Source21GroupedC19.bound
#print axioms N11Formalization.C450Source21GroupedC19.valid0
#print axioms N11Formalization.C450Source21GroupedC19.valid1
#print axioms N11Formalization.C450Source21GroupedC19.valid2
#print axioms N11Formalization.C450Source21GroupedC19.valid3
#print axioms N11Formalization.C450Source21GroupedC19.valid4
#print axioms N11Formalization.C450Source21GroupedC19.valid5
#print axioms N11Formalization.C450Source21GroupedC19.valid6
#print axioms N11Formalization.C450Source21GroupedC19.valid7
#print axioms N11Formalization.C450Source21GroupedC19.valid8
#print axioms N11Formalization.C450Source21GroupedC19.valid9
#print axioms N11Formalization.C450Source21GroupedC19.valid10
#print axioms N11Formalization.C450Source21GroupedC19.bound
#print axioms N11Formalization.C450Source21GroupedC19.endpoint_checks
