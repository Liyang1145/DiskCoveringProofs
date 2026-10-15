import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((9:ℚ)/16),((5:ℚ)/8),((2704258263:ℚ)/5000000000),((35878437:ℚ)/62500000),((33298324367:ℚ)/51500000000),((47478437:ℚ)/62000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7789566591:ℚ)/10000000000),((-150576878947791839087109065760556710654875344040617:ℚ)/509762450000000000000000000000000000000000000000000),((-49571464648257524616747:ℚ)/115520000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((1412123607:ℚ)/2500000000),((747556967:ℚ)/1250000000),((17189112463:ℚ)/26700000000),((979556967:ℚ)/1287500000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7329215217:ℚ)/10000000000),((-23307855567704258527140599066793827772101743349790463039:ℚ)/79243382876586914062500000000000000000000000000000000000),((-19598347789031864141468307:ℚ)/46208000000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((1472073357:ℚ)/2500000000),((6100344649:ℚ)/10000000000),((17728660213:ℚ)/27175000000),((2652114883:ℚ)/3560000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3422182377:ℚ)/5000000000),((-100222930768037866323085277455228243535132926681989482495593:ℚ)/333187806544400000000000000000000000000000000000000000000000),((-65791473013668140175908577:ℚ)/155648000000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((3004065907:ℚ)/5000000000),((6220193887:ℚ)/10000000000),((35996593163:ℚ)/55300000000),((8076193887:ℚ)/10870000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1647750233:ℚ)/2500000000),((-11508133209376445872111227851420882426648938773545145410653:ℚ)/38356497080754589843750000000000000000000000000000000000000),((-1242122936109396426492422147:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((9:ℚ)/16),((5:ℚ)/8),((1531983077:ℚ)/2500000000),((1268001099:ℚ)/2000000000),((18267847693:ℚ)/28125000000),((20749381:ℚ)/28000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3164573633:ℚ)/5000000000),((-4330840022788010986362742466502116247839919277:ℚ)/14470312500000000000000000000000000000000000000),((-49359583592351878381342763:ℚ)/118292480000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((3123848431:ℚ)/5000000000),((6459781381:ℚ)/10000000000),((37074635879:ℚ)/57200000000),((923975709:ℚ)/1250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3028837097:ℚ)/5000000000),((-74532241166246034424064435147283866949376434667831908751:ℚ)/249621582031250000000000000000000000000000000000000000000),((-1225638022815755388358050443:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((6367427297:ℚ)/10000000000),((6579523327:ℚ)/10000000000),((75226845673:ℚ)/116300000000),((766865757:ℚ)/1040000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5775196237:ℚ)/10000000000),((-2832748429032032013868934550286099628585768293283888799383:ℚ)/9509101097600000000000000000000000000000000000000000000000),((-1217068304460096833749980227:ℚ)/2957312000000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((6487125313:ℚ)/10000000000),((3349616497:ℚ)/5000000000),((76304127817:ℚ)/118200000000),((4277616497:ℚ)/5815000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1369995541:ℚ)/2500000000),((-10632508184455925362149903252903005575741993020220934309081:ℚ)/35770325345697070312500000000000000000000000000000000000000),((-302070124971333845933815267:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((6606792497:ℚ)/10000000000),((6818911941:ℚ)/10000000000),((77381132473:ℚ)/120100000000),((8674911941:ℚ)/11820000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((5169820149:ℚ)/10000000000),((-40887329313142778857926551514304082952069234599741319816693:ℚ)/137846170757162500000000000000000000000000000000000000000000),((-1199274669408378465335246603:ℚ)/2957312000000000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((3363215167:ℚ)/5000000000),((6938561623:ℚ)/10000000000),((39228936503:ℚ)/61000000000),((8794561623:ℚ)/12010000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1210451717:ℚ)/2500000000),((-11925592483536185802845064557343043560529273991752327208197:ℚ)/40287350745756250000000000000000000000000000000000000000000),((-1190050869994874250029187827:ℚ)/2957312000000000000000000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((6846040217:ℚ)/10000000000),((448611161:ℚ)/625000000),((79534361953:ℚ)/125800000000),((564611161:ℚ)/762500000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((4492000491:ℚ)/10000000000),((-79197788273757240617986004520176420022420717538492950259:ℚ)/274056975772094726562500000000000000000000000000000000000),((-4560620501268251238186323:ℚ)/11552000000000000000000000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((7085181253:ℚ)/10000000000),((7416893813:ℚ)/10000000000),((81686631277:ℚ)/129600000000),((9272893813:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((740368561:ℚ)/2000000000),((-12467456111050045263280730728045818873533277879325859201:ℚ)/43263343350000000000000000000000000000000000000000000000),((-1147547697983984905844824747:ℚ)/2957312000000000000000000000)⟩
theorem valid11 : Valid source30 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source30 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((1464845023:ℚ)/2000000000),((9327032693:ℚ)/10000000000),((16767605207:ℚ)/32000000000),((11183032693:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((2702138611:ℚ)/10000000000),((-107194640845997992758864234813479125315321911132290981:ℚ)/503884800000000000000000000000000000000000000000000000),((-9319607665596881:ℚ)/24320000000000000)⟩
theorem valid12 : Valid source30 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((1154239607:ℚ)/1250000000),((13138896109:ℚ)/10000000000),((549050281:ℚ)/1200000000),((14994896109:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-481690587920976432562924567255483231:ℚ)/3072000000000000000000000000000000000),((-79028809:ℚ)/204800000)⟩
theorem valid13 : Valid source30 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC26
#check @N11Formalization.C450Source30GroupedC26.bound
#print axioms N11Formalization.C450Source30GroupedC26.valid0
#print axioms N11Formalization.C450Source30GroupedC26.valid1
#print axioms N11Formalization.C450Source30GroupedC26.valid2
#print axioms N11Formalization.C450Source30GroupedC26.valid3
#print axioms N11Formalization.C450Source30GroupedC26.valid4
#print axioms N11Formalization.C450Source30GroupedC26.valid5
#print axioms N11Formalization.C450Source30GroupedC26.valid6
#print axioms N11Formalization.C450Source30GroupedC26.valid7
#print axioms N11Formalization.C450Source30GroupedC26.valid8
#print axioms N11Formalization.C450Source30GroupedC26.valid9
#print axioms N11Formalization.C450Source30GroupedC26.valid10
#print axioms N11Formalization.C450Source30GroupedC26.valid11
#print axioms N11Formalization.C450Source30GroupedC26.valid12
#print axioms N11Formalization.C450Source30GroupedC26.valid13
#print axioms N11Formalization.C450Source30GroupedC26.bound
#print axioms N11Formalization.C450Source30GroupedC26.endpoint_checks
