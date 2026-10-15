import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((3003200939:ℚ)/5000000000),((3277022651:ℚ)/5000000000),((3454400313:ℚ)/17800000000),((7117022651:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6594716909:ℚ)/10000000000),((3839128866074405203694560193999906744197:ℚ)/30204737408000000000000000000000000000000),((-30109983200173966054595081:ℚ)/92416000000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((1297339093:ℚ)/2000000000),((6793745327:ℚ)/10000000000),((4241339093:ℚ)/22120000000),((14473745327:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2740533847:ℚ)/5000000000),((4983129575810943091527696326527795401260048429587691574715861:ℚ)/41577273949050000000000000000000000000000000000000000000000000),((-128730026124795821886524049:ℚ)/369664000000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((3363282643:ℚ)/5000000000),((432096179:ℚ)/625000000),((10723282643:ℚ)/56250000000),((912096179:ℚ)/3456250000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((605178173:ℚ)/1250000000),((349385755275528717781903691349177887458739233701918673:ℚ)/2985949388122558593750000000000000000000000000000000000),((-518991797331485856649521:ℚ)/1444000000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((6846439301:ℚ)/10000000000),((1406659459:ℚ)/2000000000),((1960585391:ℚ)/10400000000),((2942659459:ℚ)/11250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((449079109:ℚ)/1000000000),((58464506215043858097200642998775839035244095781992416053:ℚ)/501306152343750000000000000000000000000000000000000000000),((-5390612437748359718506361:ℚ)/14786560000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((1393255093:ℚ)/2000000000),((715302237:ℚ)/1000000000),((4337255093:ℚ)/23260000000),((1483302237:ℚ)/5720000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2056333201:ℚ)/5000000000),((46000353229357869453336496124166159039310049570002408557417:ℚ)/395519173778300000000000000000000000000000000000000000000000),((-4099879791705681590615467:ℚ)/11089920000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((1771518917:ℚ)/2500000000),((3636357861:ℚ)/5000000000),((5451518917:ℚ)/29550000000),((7476357861:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3698588529:ℚ)/10000000000),((172955993975077155677590321850636451850192621028460714942481:ℚ)/1490430222737377929687500000000000000000000000000000000000000),((-103915486133275476637264603:ℚ)/277248000000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((7205841673:ℚ)/10000000000),((7512013279:ℚ)/10000000000),((21925841673:ℚ)/122000000000),((15192013279:ℚ)/59100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1617367261:ℚ)/5000000000),((563572296962663760297444830733205288762142072218871565860099:ℚ)/4800673057443750000000000000000000000000000000000000000000000),((-140100430867857389151510321:ℚ)/369664000000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((7445277587:ℚ)/10000000000),((7990288907:ℚ)/10000000000),((22165277587:ℚ)/129600000000),((15670288907:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((202127019:ℚ)/1000000000),((278948853782026107100368686947778691582263470926035856527383:ℚ)/2326909907812500000000000000000000000000000000000000000000000),((-94923444780540869:ℚ)/243200000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((7923805067:ℚ)/10000000000),((1237532011:ℚ)/1250000000),((22643805067:ℚ)/160000000000),((2197532011:ℚ)/8100000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((27478452303952856717377884634491751323499391224623599:ℚ)/207594140625000000000000000000000000000000000000000000),((-50952251:ℚ)/128000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((2458634163:ℚ)/2500000000),((3427979811:ℚ)/2500000000),((6138634163:ℚ)/55200000000),((5347979811:ℚ)/20000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1551116330243246698741544059137775407637:ℚ)/9522000000000000000000000000000000000000),((-50952251:ℚ)/128000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
private theorem node0_2 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_10
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_10
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9]
theorem packet_count : packets.length = 10 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC18
#check @N11Formalization.C450Source25GroupedC18.bound
#print axioms N11Formalization.C450Source25GroupedC18.valid0
#print axioms N11Formalization.C450Source25GroupedC18.valid1
#print axioms N11Formalization.C450Source25GroupedC18.valid2
#print axioms N11Formalization.C450Source25GroupedC18.valid3
#print axioms N11Formalization.C450Source25GroupedC18.valid4
#print axioms N11Formalization.C450Source25GroupedC18.valid5
#print axioms N11Formalization.C450Source25GroupedC18.valid6
#print axioms N11Formalization.C450Source25GroupedC18.valid7
#print axioms N11Formalization.C450Source25GroupedC18.valid8
#print axioms N11Formalization.C450Source25GroupedC18.valid9
#print axioms N11Formalization.C450Source25GroupedC18.bound
#print axioms N11Formalization.C450Source25GroupedC18.endpoint_checks
