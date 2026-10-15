import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((6036244811:ℚ)/10000000000),((1639482177:ℚ)/2500000000),((26428734433:ℚ)/106800000000),((2199482177:ℚ)/6200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6530360797:ℚ)/10000000000),((142699109287670157967636830851723748131:ℚ)/4247541198000000000000000000000000000000),((-2402374909164270803751703:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((1628235269:ℚ)/2500000000),((1359220603:ℚ)/2000000000),((88160833:ℚ)/350000000),((1807220603:ℚ)/5340000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2707214607:ℚ)/5000000000),((479562513624404797820444344928637014627163146665443929:ℚ)/15544566450000000000000000000000000000000000000000000000),((-1601701519948757275469663:ℚ)/9241600000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((3375600681:ℚ)/5000000000),((6915173017:ℚ)/10000000000),((14286802043:ℚ)/56250000000),((9155173017:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4771313187:ℚ)/10000000000),((45420983766724736718381418436605099909323084277149534319:ℚ)/1528806086718750000000000000000000000000000000000000000000),((-40844152026448042302948423:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((1717578039:ℚ)/2500000000),((1758558087:ℚ)/2500000000),((7232734117:ℚ)/28600000000),((2318558087:ℚ)/7031250000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1104471147:ℚ)/2500000000),((145545773572546669943119324706658426452105152115942832673:ℚ)/4936364293098449707031250000000000000000000000000000000000),((-2577362805605432185317383:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/16),((1:ℚ)/4),((6989410913:ℚ)/10000000000),((3546879089:ℚ)/5000000000),((29288232739:ℚ)/115350000000),((4666879089:ℚ)/14300000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1008960481:ℚ)/2500000000),((78339045281783285502527388595812136518996895156271943837961:ℚ)/2701971837073437500000000000000000000000000000000000000000000),((-10409574341678411200953047:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((1762238991:ℚ)/2500000000),((3576640767:ℚ)/5000000000),((7366716973:ℚ)/29075000000),((4696640767:ℚ)/14418750000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((47892889:ℚ)/125000000),((1085072170384978823276221482921665380468322099210563334989:ℚ)/37542095451569885253906250000000000000000000000000000000000),((-10458735110359822838810423:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/16),((1:ℚ)/4),((3554249113:ℚ)/5000000000),((7212802477:ℚ)/10000000000),((14822747339:ℚ)/58625000000),((9452802477:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1808046263:ℚ)/5000000000),((243432763938661206244869940506809223861174847822790743129013:ℚ)/8447435445992846679687500000000000000000000000000000000000000),((-2212184989009403258047637:ℚ)/12160000000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((1433607553:ℚ)/2000000000),((1454464213:ℚ)/2000000000),((5964822659:ℚ)/23640000000),((1902464213:ℚ)/5862500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1693869223:ℚ)/5000000000),((3159960850837348972099642307195110337921630647468049641957:ℚ)/109962234134609985351562500000000000000000000000000000000000),((-1689120825677331725265983:ℚ)/9241600000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((7227574649:ℚ)/10000000000),((1847837851:ℚ)/2500000000),((30002723947:ℚ)/120100000000),((802612617:ℚ)/2462500000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((3143528929:ℚ)/10000000000),((3895196506191706874216291651440045496677030683173424182857:ℚ)/134615401130041503906250000000000000000000000000000000000000),((-2651068998302929225699007:ℚ)/14440000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((114791261:ℚ)/156250000),((7510372981:ℚ)/10000000000),((474373783:ℚ)/1906250000),((9750372981:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1294674421:ℚ)/5000000000),((18124194644113703604662093572161956918644636035913089145749:ℚ)/629489855402441406250000000000000000000000000000000000000000),((-42809656844018551602352127:ℚ)/231040000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((2389023:ℚ)/3200000),((7748391443:ℚ)/10000000000),((9829469:ℚ)/40256000),((9988391443:ℚ)/30500000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((376550207:ℚ)/2000000000),((511793953898570579059898521079770990885652900151348375715243:ℚ)/17539646449414062500000000000000000000000000000000000000000000),((-727674868569:ℚ)/3891200000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((1925945343:ℚ)/2500000000),((499148713:ℚ)/625000000),((7857836029:ℚ)/32400000000),((639148713:ℚ)/1965625000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((144285280936822226343141549291811153917038764112672029247:ℚ)/4982783746426391601562500000000000000000000000000000000000),((-3023911:ℚ)/16000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((7941831473:ℚ)/10000000000),((2472361699:ℚ)/2500000000),((32145494419:ℚ)/160000000000),((1010787233:ℚ)/2700000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((87581921297623775771573367785800125828764071805969:ℚ)/2562890625000000000000000000000000000000000000000000),((-3023911:ℚ)/16000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((9845289177:ℚ)/10000000000),((13693044091:ℚ)/10000000000),((37855867531:ℚ)/220800000000),((15933044091:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((3260956704154022038752983245061461078153:ℚ)/76176000000000000000000000000000000000000),((-3023911:ℚ)/16000000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source15 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source15 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source15 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC20
#check @N11Formalization.C450Source15GroupedC20.bound
#print axioms N11Formalization.C450Source15GroupedC20.valid0
#print axioms N11Formalization.C450Source15GroupedC20.valid1
#print axioms N11Formalization.C450Source15GroupedC20.valid2
#print axioms N11Formalization.C450Source15GroupedC20.valid3
#print axioms N11Formalization.C450Source15GroupedC20.valid4
#print axioms N11Formalization.C450Source15GroupedC20.valid5
#print axioms N11Formalization.C450Source15GroupedC20.valid6
#print axioms N11Formalization.C450Source15GroupedC20.valid7
#print axioms N11Formalization.C450Source15GroupedC20.valid8
#print axioms N11Formalization.C450Source15GroupedC20.valid9
#print axioms N11Formalization.C450Source15GroupedC20.valid10
#print axioms N11Formalization.C450Source15GroupedC20.valid11
#print axioms N11Formalization.C450Source15GroupedC20.valid12
#print axioms N11Formalization.C450Source15GroupedC20.valid13
#print axioms N11Formalization.C450Source15GroupedC20.bound
#print axioms N11Formalization.C450Source15GroupedC20.endpoint_checks
