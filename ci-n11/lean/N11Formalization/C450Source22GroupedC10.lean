import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((1613871339:ℚ)/2500000000),((3380266171:ℚ)/5000000000),((-17261863197:ℚ)/49600000000),((-3161614017:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5559376701:ℚ)/10000000000),((32253478103879160503872103631141960237902018575238917001:ℚ)/206753765869140625000000000000000000000000000000000000000),((4254412410552527895927911:ℚ)/57760000000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((1338927773:ℚ)/2000000000),((1720023303:ℚ)/2500000000),((-8840163121:ℚ)/25750000000),((-2672783319:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1232729647:ℚ)/2500000000),((14117337222151422154840895132428100477104813158211185551:ℚ)/92886739724218750000000000000000000000000000000000000000),((2407890098151728701530039:ℚ)/36966400000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((6814170249:ℚ)/10000000000),((1399924989:ℚ)/2000000000),((-7239474923:ℚ)/20980000000),((-4574170249:ℚ)/17800000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((2293810791:ℚ)/5000000000),((701007222297128011451873598526670245361617849773456130327:ℚ)/4621953006250000000000000000000000000000000000000000000000),((56232926871215799123222191:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-7:ℚ)/16),((-3:ℚ)/8),((1386734713:ℚ)/2000000000),((7059380373:ℚ)/10000000000),((-36615662611:ℚ)/106800000000),((-2816204139:ℚ)/10775000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4218684449:ℚ)/10000000000),((610999517783164117222609336221500358033326893100750071:ℚ)/4077304572486877441406250000000000000000000000000000000),((2090004525477119504822479:ℚ)/36966400000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((6829507:ℚ)/9765625),((13904549:ℚ)/19531250),((-289327372:ℚ)/841796875),((-111408168:ℚ)/424609375),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((804480923:ℚ)/2000000000),((7719490503071797560667668896546159968175208315042817:ℚ)/51554435099754482507705688476562500000000000000000000),((383390516137345538247:ℚ)/7050781250000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((220410947:ℚ)/312500000),((1794717817:ℚ)/2500000000),((-9363024719:ℚ)/27175000000),((-3497929:ℚ)/13281250),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((1908320617:ℚ)/5000000000),((148832371271763215401484067114783666341850483983:ℚ)/994732789695262908935546875000000000000000000000),((47117944215657248123019:ℚ)/902500000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((889109893:ℚ)/1250000000),((3619303541:ℚ)/5000000000),((-18935124787:ℚ)/54825000000),((-261047097:ℚ)/987500000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3599763621:ℚ)/10000000000),((358528624277625421818457142946726504963774288578749:ℚ)/2398013019561767578125000000000000000000000000000000),((722517943671880553476759:ℚ)/14440000000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((1793150463:ℚ)/2500000000),((912292087:ℚ)/1250000000),((-4786044609:ℚ)/13825000000),((-3699451389:ℚ)/13943750000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3369621383:ℚ)/10000000000),((6249740848062584392786852338134419111489873252987575493:ℚ)/41830773300600051879882812500000000000000000000000000000),((2764304892944985950424479:ℚ)/57760000000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((3616159293:ℚ)/5000000000),((7358060267:ℚ)/10000000000),((-399035277:ℚ)/1150000000),((-2496159293:ℚ)/9375000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((48801223:ℚ)/156250000),((103620321909812341866678833796834632351736334471368671:ℚ)/694021582603454589843750000000000000000000000000000000),((10552990176030893277311159:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((14584059:ℚ)/20000000),((7477489893:ℚ)/10000000000),((-39542429251:ℚ)/112500000000),((-30312177:ℚ)/114400000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((357067521:ℚ)/1250000000),((6342518438437901448919379731950343374328655927119:ℚ)/42108580800000000000000000000000000000000000000000),((160761567524274676871:ℚ)/3696640000000000000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((1852858613:ℚ)/2500000000),((1543256613:ℚ)/2000000000),((-8242796291:ℚ)/22880000000),((-1292858613:ℚ)/4925000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2232242837:ℚ)/10000000000),((2043556618653348977165029525072015000858405501042755677:ℚ)/13345804919433593750000000000000000000000000000000000000),((2258330393384774816779879:ℚ)/57760000000000000000000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/16),((-3:ℚ)/8),((7650180693:ℚ)/10000000000),((397749753:ℚ)/500000000),((-2144248271:ℚ)/5910000000),((-16230542079:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((63979316882576729126111963289878681687006577160660980375343:ℚ)/419205534375000000000000000000000000000000000000000000000000),((4111743:ℚ)/128000000)⟩
theorem valid11 : Valid source22 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source22 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((1972212181:ℚ)/2500000000),((131753193:ℚ)/156250000),((-722272351:ℚ)/1906250000),((-1412212181:ℚ)/5400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1570871731931568809505495941078638176533503066468468429:ℚ)/10005525000000000000000000000000000000000000000000000000),((4111743:ℚ)/128000000)⟩
theorem valid12 : Valid source22 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((836597793:ℚ)/1000000000),((1292366501:ℚ)/1250000000),((-7446565507:ℚ)/16200000000),((-1837793379:ℚ)/8000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((23320612909839515385753591290623048070596679201936385773:ℚ)/129600000000000000000000000000000000000000000000000000000),((4111743:ℚ)/128000000)⟩
theorem valid13 : Valid source22 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((10272462081:ℚ)/10000000000),((14146812621:ℚ)/10000000000),((-86227688347:ℚ)/160000000000),((-8032462081:ℚ)/36800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((24098585488028024112230945791609607290256135932382863661:ℚ)/116803200000000000000000000000000000000000000000000000000),((4111743:ℚ)/128000000)⟩
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
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source22 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source22 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
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
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC10
#check @N11Formalization.C450Source22GroupedC10.bound
#print axioms N11Formalization.C450Source22GroupedC10.valid0
#print axioms N11Formalization.C450Source22GroupedC10.valid1
#print axioms N11Formalization.C450Source22GroupedC10.valid2
#print axioms N11Formalization.C450Source22GroupedC10.valid3
#print axioms N11Formalization.C450Source22GroupedC10.valid4
#print axioms N11Formalization.C450Source22GroupedC10.valid5
#print axioms N11Formalization.C450Source22GroupedC10.valid6
#print axioms N11Formalization.C450Source22GroupedC10.valid7
#print axioms N11Formalization.C450Source22GroupedC10.valid8
#print axioms N11Formalization.C450Source22GroupedC10.valid9
#print axioms N11Formalization.C450Source22GroupedC10.valid10
#print axioms N11Formalization.C450Source22GroupedC10.valid11
#print axioms N11Formalization.C450Source22GroupedC10.valid12
#print axioms N11Formalization.C450Source22GroupedC10.valid13
#print axioms N11Formalization.C450Source22GroupedC10.valid14
#print axioms N11Formalization.C450Source22GroupedC10.bound
#print axioms N11Formalization.C450Source22GroupedC10.endpoint_checks
