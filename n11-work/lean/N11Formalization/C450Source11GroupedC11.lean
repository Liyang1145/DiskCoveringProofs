import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((3151530933:ℚ)/5000000000),((3288405759:ℚ)/5000000000),((-8425217277:ℚ)/24800000000),((-2511530933:ℚ)/10300000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1185705127:ℚ)/2000000000),((22055739252097667838596610965942632652084410227536671961:ℚ)/635147568750000000000000000000000000000000000000000000000),((16070512798931575866238419:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((6540910571:ℚ)/10000000000),((6814692419:ℚ)/10000000000),((-17564077257:ℚ)/51500000000),((-1753636857:ℚ)/7120000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1335647783:ℚ)/2500000000),((2005863044654303723230944770725308252214003800064536079:ℚ)/58089445600000000000000000000000000000000000000000000000),((63022572089307977208392939:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((6778734411:ℚ)/10000000000),((6933622859:ℚ)/10000000000),((-5973622859:ℚ)/17800000000),((-5498734411:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((938362729:ℚ)/2000000000),((193072977325367593428648662422343237078270037597118496659:ℚ)/5715426488350000000000000000000000000000000000000000000000),((61694244222419267110370619:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((6897637823:ℚ)/10000000000),((6993085729:ℚ)/10000000000),((-18099257187:ℚ)/54350000000),((-1872545941:ℚ)/7310000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((866605741:ℚ)/2000000000),((22179354367204845987018701352359979603157384223792129787:ℚ)/663440074245312500000000000000000000000000000000000000000),((61030601009847009690663059:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((1739271883:ℚ)/2500000000),((7052547087:ℚ)/10000000000),((-6092547087:ℚ)/18275000000),((-1419271883:ℚ)/5530000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((517850391:ℚ)/1250000000),((1209829980835249121007645168475628350693533609500147779:ℚ)/36217133082128906250000000000000000000000000000000000000),((60717530203312157105634931:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((1403307191:ℚ)/2000000000),((711200697:ℚ)/1000000000),((-1845602091:ℚ)/5530000000),((-1147307191:ℚ)/4462000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3943970543:ℚ)/10000000000),((640559496276034431112471806615240979331510265522218967:ℚ)/19189950913196875000000000000000000000000000000000000000),((604047807054153785214691:ℚ)/9241600000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((11321573:ℚ)/16000000),((7171465417:ℚ)/10000000000),((-18634396251:ℚ)/55775000000),((-1030397:ℚ)/4000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1867576361:ℚ)/5000000000),((348829925912364360535713614944246237921928809:ℚ)/10457812500000000000000000000000000000000000000),((60092352323219623556076611:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-3:ℚ)/8),((-5:ℚ)/16),((3567714537:ℚ)/5000000000),((7201194113:ℚ)/10000000000),((-6241194113:ℚ)/18750000000),((-2927714537:ℚ)/11297500000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((3514566147:ℚ)/10000000000),((897465656761057576294037391512414879068999682364829171:ℚ)/27036366316113281250000000000000000000000000000000000000),((59761152882903911920363731:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((17912879:ℚ)/25000000),((7230922463:ℚ)/10000000000),((-18812767389:ℚ)/56487500000),((-14712879:ℚ)/56725000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((3399147101:ℚ)/10000000000),((427680807272613262822699581714635462893076287769:ℚ)/12888010493547607421875000000000000000000000000000),((59605141014178644475434131:ℚ)/924160000000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-3:ℚ)/8),((-5:ℚ)/16),((7194873833:ℚ)/10000000000),((907581309:ℚ)/1250000000),((-2362743927:ℚ)/7090625000),((-1971624611:ℚ)/7595000000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((3279832737:ℚ)/10000000000),((206109861737158279059909840661574632267175891213246899031:ℚ)/6212949846539843750000000000000000000000000000000000000000),((928893895397504115001019:ℚ)/14440000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((288983831:ℚ)/400000000),((227824317:ℚ)/312500000),((-197824317:ℚ)/593359375),((-237783831:ℚ)/915200000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((3156180761:ℚ)/10000000000),((241355077139266259519919613960545387041882286544000729:ℚ)/7277560517427200000000000000000000000000000000000000000),((28951834836325649832943:ℚ)/451250000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((7254317431:ℚ)/10000000000),((7349832493:ℚ)/10000000000),((-1742681589:ℚ)/5200000000),((-5974317431:ℚ)/23070000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1513829587:ℚ)/5000000000),((3891801571638473503991015893267097056158138112866761:ℚ)/116908864569580078125000000000000000000000000000000000),((59156992022608505921085451:ℚ)/924160000000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((7313759897:ℚ)/10000000000),((7409285543:ℚ)/10000000000),((-6449285543:ℚ)/19225000000),((-6033759897:ℚ)/23260000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((688313103:ℚ)/2500000000),((2012198024621049689531835764965340021043919522359867319673:ℚ)/60483301372150000000000000000000000000000000000000000000000),((3097149804811267226682929:ℚ)/48640000000000000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((7373201259:ℚ)/10000000000),((7528187873:ℚ)/10000000000),((-19704563619:ℚ)/58150000000),((-6093201259:ℚ)/23640000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1224572493:ℚ)/5000000000),((29795119141238039006621006528367291642253319518639053131:ℚ)/889156879900000000000000000000000000000000000000000000000),((58574695014157988969476371:ℚ)/924160000000000000000000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((3746040389:ℚ)/5000000000),((242686821:ℚ)/312500000),((-212686821:ℚ)/615625000),((-3106040389:ℚ)/12200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((13181441:ℚ)/78125000),((227822020566553454608107092286362348456592714980419114139:ℚ)/6707288550000000000000000000000000000000000000000000000000),((3810702967699259:ℚ)/60800000000000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((1545965539:ℚ)/2000000000),((8241507897:ℚ)/10000000000),((-21844523691:ℚ)/61000000000),((-429988513:ℚ)/1728000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((22815365277195340549481896997465465132674941485573959:ℚ)/655722086400000000000000000000000000000000000000000000),((3967237:ℚ)/64000000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((2051319507:ℚ)/2500000000),((5071561319:ℚ)/5000000000),((-4591561319:ℚ)/10800000000),((-1731319507:ℚ)/8000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3385054060779426524756143843168358278013615866019274521:ℚ)/86400000000000000000000000000000000000000000000000000000),((3967237:ℚ)/64000000)⟩
theorem valid16 : Valid source11 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((101066511:ℚ)/100000000),((13945017219:ℚ)/10000000000),((-38955051657:ℚ)/80000000000),((-88266511:ℚ)/441600000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((17918505938635986582097358652248980477303911520213:ℚ)/403671859200000000000000000000000000000000000000000),((3967237:ℚ)/64000000)⟩
theorem valid17 : Valid source11 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC11
#check @N11Formalization.C450Source11GroupedC11.bound
#print axioms N11Formalization.C450Source11GroupedC11.valid0
#print axioms N11Formalization.C450Source11GroupedC11.valid1
#print axioms N11Formalization.C450Source11GroupedC11.valid2
#print axioms N11Formalization.C450Source11GroupedC11.valid3
#print axioms N11Formalization.C450Source11GroupedC11.valid4
#print axioms N11Formalization.C450Source11GroupedC11.valid5
#print axioms N11Formalization.C450Source11GroupedC11.valid6
#print axioms N11Formalization.C450Source11GroupedC11.valid7
#print axioms N11Formalization.C450Source11GroupedC11.valid8
#print axioms N11Formalization.C450Source11GroupedC11.valid9
#print axioms N11Formalization.C450Source11GroupedC11.valid10
#print axioms N11Formalization.C450Source11GroupedC11.valid11
#print axioms N11Formalization.C450Source11GroupedC11.valid12
#print axioms N11Formalization.C450Source11GroupedC11.valid13
#print axioms N11Formalization.C450Source11GroupedC11.valid14
#print axioms N11Formalization.C450Source11GroupedC11.valid15
#print axioms N11Formalization.C450Source11GroupedC11.valid16
#print axioms N11Formalization.C450Source11GroupedC11.valid17
#print axioms N11Formalization.C450Source11GroupedC11.bound
#print axioms N11Formalization.C450Source11GroupedC11.endpoint_checks
