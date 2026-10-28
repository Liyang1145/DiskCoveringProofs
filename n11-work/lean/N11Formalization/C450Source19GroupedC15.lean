import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((3101608027:ℚ)/5000000000),((1681666301:ℚ)/2500000000),((-321666301:ℚ)/12400000000),((2658391973:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1539928351:ℚ)/2500000000),((2304231775524796414099913978565956387:ℚ)/30505984000000000000000000000000000000),((-193069578280802571977539043:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((6681207499:ℚ)/10000000000),((6846089039:ℚ)/10000000000),((-1406089039:ℚ)/53400000000),((4838792501:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((198725017:ℚ)/400000000),((1664949365044995484878756003488756473427084265419187876979:ℚ)/22840995600000000000000000000000000000000000000000000000000),((-872682715159225850233692867:ℚ)/7393280000000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((106259991:ℚ)/156250000),((6965489531:ℚ)/10000000000),((-1525489531:ℚ)/54350000000),((73740009:ℚ)/1698437500),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((925532601:ℚ)/2000000000),((138793304353563506767810613467214089989425417461353:ℚ)/1913853739202022552490234375000000000000000000000000),((-657568024664669365051681:ℚ)/5415000000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((276801909:ℚ)/400000000),((1771216969:ℚ)/2500000000),((-411216969:ℚ)/13825000000),((183998091:ℚ)/4424000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2131129369:ℚ)/5000000000),((5580163917610948270040906130033861421316553789327201:ℚ)/77308515200000000000000000000000000000000000000000000),((-4430031479847837685895881:ℚ)/35487744000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((703943361:ℚ)/1000000000),((7204225189:ℚ)/10000000000),((-196025021:ℚ)/6250000000),((49784071:ℚ)/1250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3864808647:ℚ)/10000000000),((877334658024981656727806299200100087417265532578827:ℚ)/12207031250000000000000000000000000000000000000000000),((-28441620250974645568771921:ℚ)/221798400000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((7158798209:ℚ)/10000000000),((7323562511:ℚ)/10000000000),((-1883562511:ℚ)/57200000000),((4361201791:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3424132521:ℚ)/10000000000),((502430835073373654829530066336642372193944258314176404369:ℚ)/7018096800000000000000000000000000000000000000000000000000),((-973192124578524669764566427:ℚ)/7393280000000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((454883911:ℚ)/625000000),((1488576163:ℚ)/2000000000),((-400576163:ℚ)/11630000000),((265116089:ℚ)/7268750000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1460342411:ℚ)/5000000000),((128421037171539424123962767770246645491255377360788279:ℚ)/1800198837661743164062500000000000000000000000000000000),((-3899756989903027996670507:ℚ)/28880000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((1479493539:ℚ)/2000000000),((7681463959:ℚ)/10000000000),((-747154653:ℚ)/19700000000),((274835487:ℚ)/7880000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2313793309:ℚ)/10000000000),((218119699484014682769530353927965016877606191546116099:ℚ)/3058149200000000000000000000000000000000000000000000000),((-340218682884255615482161:ℚ)/2457600000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((7636063823:ℚ)/10000000000),((8158438513:ℚ)/10000000000),((-2718438513:ℚ)/61000000000),((3883936177:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((202430984531649234904363821516469965820020567455604940389:ℚ)/2837262500000000000000000000000000000000000000000000000000),((-73837361:ℚ)/512000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((507066377:ℚ)/625000000),((629028273:ℚ)/625000000),((-289028273:ℚ)/4050000000),((212933623:ℚ)/8100000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((45545378583901892182950992822138178468492703562571617:ℚ)/622782421875000000000000000000000000000000000000000000),((-73837361:ℚ)/512000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((10019147831:ℚ)/10000000000),((1387149847:ℚ)/1000000000),((-843149847:ℚ)/8000000000),((1500852169:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((82201946611782599411656308203960676199:ℚ)/1024000000000000000000000000000000000000),((-73837361:ℚ)/512000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC15
#check @N11Formalization.C450Source19GroupedC15.bound
#print axioms N11Formalization.C450Source19GroupedC15.valid0
#print axioms N11Formalization.C450Source19GroupedC15.valid1
#print axioms N11Formalization.C450Source19GroupedC15.valid2
#print axioms N11Formalization.C450Source19GroupedC15.valid3
#print axioms N11Formalization.C450Source19GroupedC15.valid4
#print axioms N11Formalization.C450Source19GroupedC15.valid5
#print axioms N11Formalization.C450Source19GroupedC15.valid6
#print axioms N11Formalization.C450Source19GroupedC15.valid7
#print axioms N11Formalization.C450Source19GroupedC15.valid8
#print axioms N11Formalization.C450Source19GroupedC15.valid9
#print axioms N11Formalization.C450Source19GroupedC15.valid10
#print axioms N11Formalization.C450Source19GroupedC15.bound
#print axioms N11Formalization.C450Source19GroupedC15.endpoint_checks
