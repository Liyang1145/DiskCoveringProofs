import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((5:ℚ)/16),((3:ℚ)/8),((1384410437:ℚ)/2500000000),((1470384693:ℚ)/2500000000),((2472410437:ℚ)/5150000000),((7211154079:ℚ)/12400000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7544664549:ℚ)/10000000000),((-669852693578383141510893393030322020726858996561333990419:ℚ)/1841083800000000000000000000000000000000000000000000000000),((-10507749388465490437134823:ℚ)/28880000000000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((2890158847:ℚ)/5000000000),((6123789967:ℚ)/10000000000),((5066158847:ℚ)/10680000000),((29571369901:ℚ)/51500000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7066086341:ℚ)/10000000000),((-10230993996849886339276218398631396965772116331358986688063:ℚ)/28492002832031250000000000000000000000000000000000000000000),((-167451396884226099209885503:ℚ)/462080000000000000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((6022614067:ℚ)/10000000000),((624478741:ℚ)/1000000000),((10374614067:ℚ)/21740000000),((2993436223:ℚ)/5340000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((819977771:ℚ)/1250000000),((-20795745953889596987270088468154002845901794410752376409:ℚ)/57472597725000000000000000000000000000000000000000000000),((-1686022694373453152114087:ℚ)/4620800000000000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((3071816423:ℚ)/5000000000),((6365705507:ℚ)/10000000000),((5247816423:ℚ)/11060000000),((30297116521:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3147068859:ℚ)/5000000000),((-4676332570557601639407829131917134538207639825358185451659:ℚ)/13005141415264892578125000000000000000000000000000000000000),((-168170362184468928212270423:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/16),((3:ℚ)/8),((1252914301:ℚ)/2000000000),((6486548423:ℚ)/10000000000),((2123314301:ℚ)/4500000000),((30659645269:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3009284357:ℚ)/5000000000),((-6640864202262327115088516692631734013685623388244635229:ℚ)/18579240637207031250000000000000000000000000000000000000),((-167700825606643710990499183:ℚ)/462080000000000000000000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((25541737:ℚ)/40000000),((206478751:ℚ)/312500000),((42949737:ℚ)/91520000),((969436253:ℚ)/1757812500),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5731652007:ℚ)/10000000000),((-862646948311851646258512092506045113536589244954003679:ℚ)/2427189610898494720458984375000000000000000000000000000),((-326550229730386147411729:ℚ)/902500000000000000000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((6506224997:ℚ)/10000000000),((1682005987:ℚ)/2500000000),((10858224997:ℚ)/23260000000),((7846017961:ℚ)/14300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1086310309:ℚ)/2000000000),((-2822572150542703783872600400242466260733672748656462153:ℚ)/7984721875000000000000000000000000000000000000000000000),((-10415568255863686939270663:ℚ)/28880000000000000000000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((3313473697:ℚ)/5000000000),((342433177:ℚ)/500000000),((5489473697:ℚ)/11820000000),((1587299531:ℚ)/2907500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2557954501:ℚ)/5000000000),((-3991146415573042938819432423799556496679255296985006829:ℚ)/11348453472619628906250000000000000000000000000000000000),((-415167498146317021571983:ℚ)/1155200000000000000000000)⟩
theorem valid7 : Valid source36 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source36 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((1686901211:ℚ)/2500000000),((7089762141:ℚ)/10000000000),((2774901211:ℚ)/6100000000),((32469286423:ℚ)/59100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4781607649:ℚ)/10000000000),((-40659550785507916742646639118586267342901796375113199282289:ℚ)/118049337478125000000000000000000000000000000000000000000000),((-163253122345057433820121687:ℚ)/462080000000000000000000000)⟩
theorem valid8 : Valid source36 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source36 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((873592177:ℚ)/1250000000),((1514262643:ℚ)/2000000000),((1417592177:ℚ)/3240000000),((6782787929:ℚ)/12200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((504762233:ℚ)/1250000000),((-43703783004571073128550451088979237118768421987821693379:ℚ)/131832797400000000000000000000000000000000000000000000000),((-6287361258841511865327223:ℚ)/18483200000000000000000000)⟩
theorem valid9 : Valid source36 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((7470350209:ℚ)/10000000000),((2372800033:ℚ)/2500000000),((11822350209:ℚ)/32000000000),((9918400099:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1849751743:ℚ)/10000000000),((-63090878973853511532757391526791460303016408871855977341667:ℚ)/223948800000000000000000000000000000000000000000000000000000),((-85663407091339373:ℚ)/243200000000000000)⟩
theorem valid10 : Valid source36 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((9390423589:ℚ)/10000000000),((13314396823:ℚ)/10000000000),((4580807863:ℚ)/14720000000),((51143190469:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1803276140061460579754229769047492387355488417087281909:ℚ)/7475404800000000000000000000000000000000000000000000000),((-711623:ℚ)/2000000)⟩
theorem valid11 : Valid source36 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source36 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC22
#check @N11Formalization.C450Source36GroupedC22.bound
#print axioms N11Formalization.C450Source36GroupedC22.valid0
#print axioms N11Formalization.C450Source36GroupedC22.valid1
#print axioms N11Formalization.C450Source36GroupedC22.valid2
#print axioms N11Formalization.C450Source36GroupedC22.valid3
#print axioms N11Formalization.C450Source36GroupedC22.valid4
#print axioms N11Formalization.C450Source36GroupedC22.valid5
#print axioms N11Formalization.C450Source36GroupedC22.valid6
#print axioms N11Formalization.C450Source36GroupedC22.valid7
#print axioms N11Formalization.C450Source36GroupedC22.valid8
#print axioms N11Formalization.C450Source36GroupedC22.valid9
#print axioms N11Formalization.C450Source36GroupedC22.valid10
#print axioms N11Formalization.C450Source36GroupedC22.valid11
#print axioms N11Formalization.C450Source36GroupedC22.bound
#print axioms N11Formalization.C450Source36GroupedC22.endpoint_checks
