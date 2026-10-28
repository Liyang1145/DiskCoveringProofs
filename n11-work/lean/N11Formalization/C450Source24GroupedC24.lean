import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((5688593333:ℚ)/10000000000),((6242929543:ℚ)/10000000000),((17966717777:ℚ)/35600000000),((8082929543:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3625002257:ℚ)/5000000000),((-157045759264264843232476367501951591:ℚ)/5639752000000000000000000000000000000),((-219323330163022215313493:ℚ)/577600000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((6167278851:ℚ)/10000000000),((810257211:ℚ)/1250000000),((57250951957:ℚ)/110600000000),((1040257211:ℚ)/1668750000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6241091027:ℚ)/10000000000),((-75761326920940738938738159865586919101463221391394851997:ℚ)/1811918325000000000000000000000000000000000000000000000000),((-10501676960791467555041:ℚ)/27075000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/16),((1:ℚ)/2),((800803707:ℚ)/1250000000),((6601580107:ℚ)/10000000000),((7365625949:ℚ)/14062500000),((8441580107:ℚ)/13825000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2840253587:ℚ)/5000000000),((-139044391753957032769772189881396901918459176761050227:ℚ)/2896785736083984375000000000000000000000000000000000000),((-226359197044322263381693:ℚ)/577600000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((326298141:ℚ)/500000000),((6721076627:ℚ)/10000000000),((2988086987:ℚ)/5720000000),((2853692209:ℚ)/4687500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5381091173:ℚ)/10000000000),((-2553458227854519336303909466802436649710160380628877:ℚ)/53167400000000000000000000000000000000000000000000000),((-226945388518944236937453:ℚ)/577600000000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((3322734861:ℚ)/5000000000),((6840548533:ℚ)/10000000000),((30299144027:ℚ)/58150000000),((8680548533:ℚ)/14300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1266476051:ℚ)/2500000000),((-22127503983910725804275038892350607906706169857159325109:ℚ)/460850902441406250000000000000000000000000000000000000000),((-227511174706604629834173:ℚ)/577600000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((6764951663:ℚ)/10000000000),((217499907:ℚ)/312500000),((20478220547:ℚ)/39400000000),((274999907:ℚ)/454296875),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2365882287:ℚ)/5000000000),((-6875737336152777040018478934162813213755246920408122701:ℚ)/143350743750000000000000000000000000000000000000000000000),((-5345075975652511955857:ℚ)/13537500000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((6884409861:ℚ)/10000000000),((3539711613:ℚ)/5000000000),((62270869027:ℚ)/120100000000),((4459711613:ℚ)/7387500000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4374298487:ℚ)/10000000000),((-777571046762165339251248817131608559544383204188027534869:ℚ)/16240533759375000000000000000000000000000000000000000000000),((-171436205522239810993799:ℚ)/433200000000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((3501922729:ℚ)/5000000000),((7198828191:ℚ)/10000000000),((31553459103:ℚ)/61000000000),((9038828191:ℚ)/15012500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((62300033:ℚ)/156250000),((-33875494330058633657980106890823100387143237554433042347:ℚ)/709315625000000000000000000000000000000000000000000000000),((-687258866675387144147951:ℚ)/1732800000000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((7123259521:ℚ)/10000000000),((3718789151:ℚ)/5000000000),((63942816647:ℚ)/125800000000),((4638789151:ℚ)/7625000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((3560787233:ℚ)/10000000000),((-66285149962153725411525969302027059212903766799031646363:ℚ)/1555363681250000000000000000000000000000000000000000000000),((-57080169402445660031557:ℚ)/144400000000000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((7362026989:ℚ)/10000000000),((7676254557:ℚ)/10000000000),((65614188923:ℚ)/129600000000),((9516254557:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((250906461:ℚ)/1000000000),((-10686616294664141213958156719651363224877492300864031709:ℚ)/251942400000000000000000000000000000000000000000000000000),((-6053027741985387:ℚ)/15200000000000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((475044973:ℚ)/625000000),((9583642087:ℚ)/10000000000),((4205314811:ℚ)/10000000000),((11423642087:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1541943779108090698431548626600889:ℚ)/187500000000000000000000000000000000),((-3233121:ℚ)/8000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((4754104733:ℚ)/5000000000),((6696146911:ℚ)/5000000000),((1752988397:ℚ)/4800000000),((7616146911:ℚ)/10000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((323370147687819307498337:ℚ)/5760000000000000000000000),((-3233121:ℚ)/8000000)⟩
theorem valid11 : Valid source24 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source24 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source24 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC24
#check @N11Formalization.C450Source24GroupedC24.bound
#print axioms N11Formalization.C450Source24GroupedC24.valid0
#print axioms N11Formalization.C450Source24GroupedC24.valid1
#print axioms N11Formalization.C450Source24GroupedC24.valid2
#print axioms N11Formalization.C450Source24GroupedC24.valid3
#print axioms N11Formalization.C450Source24GroupedC24.valid4
#print axioms N11Formalization.C450Source24GroupedC24.valid5
#print axioms N11Formalization.C450Source24GroupedC24.valid6
#print axioms N11Formalization.C450Source24GroupedC24.valid7
#print axioms N11Formalization.C450Source24GroupedC24.valid8
#print axioms N11Formalization.C450Source24GroupedC24.valid9
#print axioms N11Formalization.C450Source24GroupedC24.valid10
#print axioms N11Formalization.C450Source24GroupedC24.valid11
#print axioms N11Formalization.C450Source24GroupedC24.bound
#print axioms N11Formalization.C450Source24GroupedC24.endpoint_checks
