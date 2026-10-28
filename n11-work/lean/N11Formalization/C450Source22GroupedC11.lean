import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((6403251171:ℚ)/10000000000),((6705229361:ℚ)/10000000000),((-13715688083:ℚ)/49600000000),((-3715251171:ℚ)/20600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5688276229:ℚ)/10000000000),((130720575552120259227440776966904181963034954454841304147:ℚ)/846863425000000000000000000000000000000000000000000000000),((57468319437855408733487543:ℚ)/4435968000000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((1328497653:ℚ)/2000000000),((682484171:ℚ)/1000000000),((-1407452513:ℚ)/5150000000),((-790897653:ℚ)/4196000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((634247951:ℚ)/1250000000),((896706245682244156765979292823693345521073659907306853:ℚ)/5944751342350000000000000000000000000000000000000000000),((652465357479184343094407:ℚ)/177438720000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((1690514781:ℚ)/2500000000),((3472211527:ℚ)/5000000000),((-7216634581:ℚ)/26225000000),((-339504927:ℚ)/1780000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((2370054703:ℚ)/5000000000),((695301413518717813000660024610540456376687165507557809:ℚ)/4621953006250000000000000000000000000000000000000000000),((-273962154723183136477897:ℚ)/277248000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((6881600483:ℚ)/10000000000),((11037461:ℚ)/15625000),((-23112383:ℚ)/83437500),((-4193600483:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((438301661:ℚ)/1000000000),((1286495694087495934379034495728673719023473036169943455783:ℚ)/8573139732525000000000000000000000000000000000000000000000),((-8385507961337641716704451:ℚ)/1478656000000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((700111391:ℚ)/1000000000),((1780935127:ℚ)/2500000000),((-3742805381:ℚ)/13587500000),((-431311391:ℚ)/2193000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3996449509:ℚ)/10000000000),((443468347696210730427247332449526606892671503681338933:ℚ)/2985480334103906250000000000000000000000000000000000000),((-153359889363730481209579:ℚ)/14786560000000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((7060860609:ℚ)/10000000000),((3591749601:ℚ)/5000000000),((-7575248803:ℚ)/27412500000),((-4372860609:ℚ)/22120000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1894655169:ℚ)/5000000000),((3999557412935043538388559841113595024712501360250345877:ℚ)/26952285084375000000000000000000000000000000000000000000),((-56463118195444816494020737:ℚ)/4435968000000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((7120600863:ℚ)/10000000000),((3621625649:ℚ)/5000000000),((-1094982421:ℚ)/3950000000),((-4432600863:ℚ)/22310000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1785404391:ℚ)/5000000000),((25401444361131445736339763491080053776825959487429887359:ℚ)/171338847439257812500000000000000000000000000000000000000),((-66937920843450728266629313:ℚ)/4435968000000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((7180334839:ℚ)/10000000000),((3651498483:ℚ)/5000000000),((-7754495449:ℚ)/27887500000),((-4492334839:ℚ)/22500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1669354821:ℚ)/5000000000),((137843061160929446703560238304599988077516169901772591829:ℚ)/930632972717285156250000000000000000000000000000000000000),((-25810799132358814663814939:ℚ)/1478656000000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((3620031349:ℚ)/5000000000),((1484493933:ℚ)/2000000000),((-3173481799:ℚ)/11250000000),((-2276031349:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3089944877:ℚ)/10000000000),((6278875108889143354103016460648996095576560927929581907:ℚ)/42108580800000000000000000000000000000000000000000000000),((-7328880806335047152411859:ℚ)/369664000000000000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((7359500683:ℚ)/10000000000),((7541918541:ℚ)/10000000000),((-1475068693:ℚ)/5200000000),((-4671500683:ℚ)/23260000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((630604543:ℚ)/2500000000),((76095254980454638788033784951005105914507727835774197473:ℚ)/511237267775000000000000000000000000000000000000000000000),((-36344695070708910002583251:ℚ)/1478656000000000000000000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((7478915999:ℚ)/10000000000),((7661344757:ℚ)/10000000000),((-16584034271:ℚ)/58150000000),((-4790915999:ℚ)/23640000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((446858359:ℚ)/2500000000),((66064952469020569557005004084453523326572792956979545297:ℚ)/444578439950000000000000000000000000000000000000000000000),((-43400209147706762771015659:ℚ)/1478656000000000000000000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((949788719:ℚ)/1250000000),((493758343:ℚ)/625000000),((-1081275029:ℚ)/3693750000),((-613788719:ℚ)/3050000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((6590851:ℚ)/312500000),((7883515011194198985007216197943509040351384082944904383:ℚ)/52400691796875000000000000000000000000000000000000000000),((-788783053551306561756299:ℚ)/23104000000000000000000000)⟩
theorem valid11 : Valid source22 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source22 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((7837036639:ℚ)/10000000000),((8377482561:ℚ)/10000000000),((-18732447683:ℚ)/61000000000),((-5149036639:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((170212443213325617316066770012333092604111009742172238911:ℚ)/1106531020800000000000000000000000000000000000000000000000),((-17514741:ℚ)/512000000)⟩
theorem valid12 : Valid source22 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((4157136529:ℚ)/5000000000),((10284635151:ℚ)/10000000000),((-24453905453:ℚ)/64800000000),((-2813136529:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((178566871895898338929064213513970166321365342936373940423:ℚ)/1036800000000000000000000000000000000000000000000000000000),((-17514741:ℚ)/512000000)⟩
theorem valid13 : Valid source22 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((2555270797:ℚ)/2500000000),((14093012377:ℚ)/10000000000),((-35879037131:ℚ)/80000000000),((-81881339:ℚ)/480000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((50796181694380762142595621927551797478388746472199:ℚ)/259200000000000000000000000000000000000000000000000),((-17514741:ℚ)/512000000)⟩
theorem valid14 : Valid source22 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source22 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((2231:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source22 nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source22 nn0 nn1 Qcell ((2231:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source22 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC11
#check @N11Formalization.C450Source22GroupedC11.bound
#print axioms N11Formalization.C450Source22GroupedC11.valid0
#print axioms N11Formalization.C450Source22GroupedC11.valid1
#print axioms N11Formalization.C450Source22GroupedC11.valid2
#print axioms N11Formalization.C450Source22GroupedC11.valid3
#print axioms N11Formalization.C450Source22GroupedC11.valid4
#print axioms N11Formalization.C450Source22GroupedC11.valid5
#print axioms N11Formalization.C450Source22GroupedC11.valid6
#print axioms N11Formalization.C450Source22GroupedC11.valid7
#print axioms N11Formalization.C450Source22GroupedC11.valid8
#print axioms N11Formalization.C450Source22GroupedC11.valid9
#print axioms N11Formalization.C450Source22GroupedC11.valid10
#print axioms N11Formalization.C450Source22GroupedC11.valid11
#print axioms N11Formalization.C450Source22GroupedC11.valid12
#print axioms N11Formalization.C450Source22GroupedC11.valid13
#print axioms N11Formalization.C450Source22GroupedC11.valid14
#print axioms N11Formalization.C450Source22GroupedC11.bound
#print axioms N11Formalization.C450Source22GroupedC11.endpoint_checks
