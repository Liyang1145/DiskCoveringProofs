import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC16
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((-1:ℚ)/16),(0:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/16),(0:ℚ),((609799967:ℚ)/1000000000),((1603529549:ℚ)/2500000000),((2716470451:ℚ)/25750000000),((28:ℚ)/155),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3197716801:ℚ)/5000000000),((1542646667251769573540229580587165482046045910648431827:ℚ)/320134863281250000000000000000000000000000000000000000000),((-1405739886675087:ℚ)/6080000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/16),(0:ℚ),((6339322221:ℚ)/10000000000),((6654895637:ℚ)/10000000000),((10625104363:ℚ)/106800000000),((448:ℚ)/2575),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((182580763:ℚ)/312500000),((14202346845135118333647287609330077897001233519825830713:ℚ)/1903416300000000000000000000000000000000000000000000000000),((-14723777547502781:ℚ)/60800000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((6580366629:ℚ)/10000000000),((1693799181:ℚ)/2500000000),((2626200819:ℚ)/27175000000),((224:ℚ)/1335),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((654967541:ℚ)/1250000000),((1050989342112321466048510857198164737507482749147203161:ℚ)/125426318652343750000000000000000000000000000000000000000),((-15389388175022069:ℚ)/60800000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((670079391:ℚ)/1000000000),((6895443507:ℚ)/10000000000),((10384556493:ℚ)/110600000000),((896:ℚ)/5435),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4913781897:ℚ)/10000000000),((1269550521952133609096686882332739466903109474833961807:ℚ)/132119044531250000000000000000000000000000000000000000000),((-1572193137211151:ℚ)/6080000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/16),(0:ℚ),((341058119:ℚ)/500000000),((1403127761:ℚ)/2000000000),((2052872239:ℚ)/22500000000),((64:ℚ)/395),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2283401117:ℚ)/5000000000),((9008189630287179043841421905649363783161403841210343:ℚ)/834274291992187500000000000000000000000000000000000000),((-802715608539959:ℚ)/3040000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/16),(0:ℚ),((6941475097:ℚ)/10000000000),((1783946311:ℚ)/2500000000),((195081053:ℚ)/2200000000),((896:ℚ)/5625),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4193544339:ℚ)/10000000000),((795118918894294477044660762310780207077605733388783:ℚ)/66550000000000000000000000000000000000000000000000000),((-16386539015327017:ℚ)/60800000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((13792451:ℚ)/19531250),((115249081:ℚ)/156250000),((154750919:ℚ)/1846875000),((112:ℚ)/715),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((118318729:ℚ)/312500000),((5238115134704392149534497786824805089750398818983:ℚ)/364559793472290039062500000000000000000000000000000),((-32653554254561:ℚ)/118750000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/16),(0:ℚ),((3651053143:ℚ)/5000000000),((7615929061:ℚ)/10000000000),((9664070939:ℚ)/122000000000),((448:ℚ)/2955),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2809103541:ℚ)/10000000000),((558459873860806727464987769676633896557838556081370804723:ℚ)/34047150000000000000000000000000000000000000000000000000000),((-8691185958007623:ℚ)/30400000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/16),(0:ℚ),((942786967:ℚ)/1250000000),((1619092181:ℚ)/2000000000),((1836907819:ℚ)/25920000000),((224:ℚ)/1525),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((24661377:ℚ)/200000000),((742424568249766181639237674083660103519557104100371147:ℚ)/36279705600000000000000000000000000000000000000000000000),((-2255702711982087:ℚ)/7600000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/16),(0:ℚ),((8022194211:ℚ)/10000000000),((2502309523:ℚ)/2500000000),((1817690477:ℚ)/40000000000),((56:ℚ)/405),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((39516425404624642905656855296356879406485600518609044381:ℚ)/1200000000000000000000000000000000000000000000000000000000),((-239539:ℚ)/800000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/16),(0:ℚ),((621067629:ℚ)/625000000),((13825339813:ℚ)/10000000000),((3454660187:ℚ)/220800000000),((14:ℚ)/125),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2615873667054745409941126344501822517990577326303337071651:ℚ)/50458982400000000000000000000000000000000000000000000000000),((-239539:ℚ)/800000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC16
#check @N11Formalization.C450Source29GroupedC16.bound
#print axioms N11Formalization.C450Source29GroupedC16.valid0
#print axioms N11Formalization.C450Source29GroupedC16.valid1
#print axioms N11Formalization.C450Source29GroupedC16.valid2
#print axioms N11Formalization.C450Source29GroupedC16.valid3
#print axioms N11Formalization.C450Source29GroupedC16.valid4
#print axioms N11Formalization.C450Source29GroupedC16.valid5
#print axioms N11Formalization.C450Source29GroupedC16.valid6
#print axioms N11Formalization.C450Source29GroupedC16.valid7
#print axioms N11Formalization.C450Source29GroupedC16.valid8
#print axioms N11Formalization.C450Source29GroupedC16.valid9
#print axioms N11Formalization.C450Source29GroupedC16.valid10
#print axioms N11Formalization.C450Source29GroupedC16.bound
#print axioms N11Formalization.C450Source29GroupedC16.endpoint_checks
