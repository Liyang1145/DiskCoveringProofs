import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((3104878539:ℚ)/5000000000),((1344367243:ℚ)/2000000000),((-512367243:ℚ)/9920000000),((1375121461:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6144800959:ℚ)/10000000000),((1483982760852632878085468682122727103:ℚ)/30505984000000000000000000000000000000),((-185064386555870418359268893:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((1337311993:ℚ)/2000000000),((273639699:ℚ)/400000000),((-107239699:ℚ)/2136000000),((151562669:ℚ)/7120000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4953329031:ℚ)/10000000000),((318597497258795133448853052832719648358290166010228663:ℚ)/6767702400000000000000000000000000000000000000000000000),((-34270564015960135903396917:ℚ)/591462400000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((3402860543:ℚ)/5000000000),((6960134707:ℚ)/10000000000),((-2800134707:ℚ)/54350000000),((1077139457:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((922532561:ℚ)/2000000000),((2939252897050665059495442079669483526423890551300354433:ℚ)/62713159326171875000000000000000000000000000000000000000),((-221472852963889923837909317:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((6924868011:ℚ)/10000000000),((7079263627:ℚ)/10000000000),((-417037661:ℚ)/7900000000),((2035131989:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2123445937:ℚ)/5000000000),((56385061834903373583644798011530373696877590565009950587:ℚ)/1207945550000000000000000000000000000000000000000000000000),((-915019391188294707151001693:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((880500183:ℚ)/1250000000),((3569411653:ℚ)/5000000000),((-496470551:ℚ)/9375000000),((239499817:ℚ)/14062500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((962207959:ℚ)/2500000000),((89661730246268304511578209127451147881642161083012817:ℚ)/1931190490722656250000000000000000000000000000000000000),((-14752315843016054659452437:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((887945419:ℚ)/1250000000),((7198379903:ℚ)/10000000000),((-3038379903:ℚ)/56725000000),((232054581:ℚ)/14181250000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1817201081:ℚ)/5000000000),((33046142609496976463166092931818106446724138051115501:ℚ)/712990179992675781250000000000000000000000000000000000),((-14979890521769326628061213:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((179078053:ℚ)/250000000),((1451586699:ℚ)/2000000000),((-619586699:ℚ)/11440000000),((44921947:ℚ)/2860000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((681429479:ℚ)/2000000000),((1691397872080722031528196083949507240870638812693067:ℚ)/36552587500000000000000000000000000000000000000000000),((-608298777389352043807997:ℚ)/9241600000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((7222677849:ℚ)/10000000000),((7317484157:ℚ)/10000000000),((-1052494719:ℚ)/19225000000),((1737322151:ℚ)/115350000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3164300671:ℚ)/10000000000),((656570569953820427337679056404239992762868415356158237:ℚ)/14211144031250000000000000000000000000000000000000000000),((-987843384890319166736710133:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((7282230611:ℚ)/10000000000),((1859144243:ℚ)/2500000000),((-819144243:ℚ)/14537500000),((1677769389:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2901945051:ℚ)/10000000000),((113573282582613674237074568379194316645567421043760811869:ℚ)/2457871479687500000000000000000000000000000000000000000000),((-1002409034047715962554169293:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((3700663763:ℚ)/5000000000),((472228681:ℚ)/625000000),((-212228681:ℚ)/3693750000),((779336237:ℚ)/59100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2291541347:ℚ)/10000000000),((19817172045991009674008841246950073136909305311406945239:ℚ)/430052231250000000000000000000000000000000000000000000000),((-714363800170235806460357:ℚ)/10240000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((7520413417:ℚ)/10000000000),((3837365219:ℚ)/5000000000),((-1757365219:ℚ)/30025000000),((1439586583:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1448464491:ℚ)/10000000000),((497687394967645100531558527163164458470682573143381974183:ℚ)/10827022506250000000000000000000000000000000000000000000000),((-1060675057865220687424351637:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((7639488803:ℚ)/10000000000),((407546099:ℚ)/500000000),((-199546099:ℚ)/3050000000),((1320511197:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((131352727592997681824798834674945714417941996252575705997:ℚ)/2837262500000000000000000000000000000000000000000000000000),((-74802479:ℚ)/1024000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((1014461823:ℚ)/1250000000),((628409567:ℚ)/625000000),((-122803189:ℚ)/1350000000),((105538177:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((26348299755779685089294567022213786435754341690269371:ℚ)/553584375000000000000000000000000000000000000000000000),((-74802479:ℚ)/1024000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((1001902373:ℚ)/1000000000),((3464702671:ℚ)/2500000000),((-2424702671:ℚ)/20000000000),((-1534817:ℚ)/320000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2677928115128880489526795554497715835530248169527:ℚ)/51200000000000000000000000000000000000000000000000),((-74802479:ℚ)/1024000000)⟩
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
end N11Formalization.C450Source15GroupedC15
#check @N11Formalization.C450Source15GroupedC15.bound
#print axioms N11Formalization.C450Source15GroupedC15.valid0
#print axioms N11Formalization.C450Source15GroupedC15.valid1
#print axioms N11Formalization.C450Source15GroupedC15.valid2
#print axioms N11Formalization.C450Source15GroupedC15.valid3
#print axioms N11Formalization.C450Source15GroupedC15.valid4
#print axioms N11Formalization.C450Source15GroupedC15.valid5
#print axioms N11Formalization.C450Source15GroupedC15.valid6
#print axioms N11Formalization.C450Source15GroupedC15.valid7
#print axioms N11Formalization.C450Source15GroupedC15.valid8
#print axioms N11Formalization.C450Source15GroupedC15.valid9
#print axioms N11Formalization.C450Source15GroupedC15.valid10
#print axioms N11Formalization.C450Source15GroupedC15.valid11
#print axioms N11Formalization.C450Source15GroupedC15.valid12
#print axioms N11Formalization.C450Source15GroupedC15.valid13
#print axioms N11Formalization.C450Source15GroupedC15.bound
#print axioms N11Formalization.C450Source15GroupedC15.endpoint_checks
