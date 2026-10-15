import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((570985881:ℚ)/1000000000),((781369229:ℚ)/1250000000),((1460300389:ℚ)/1780000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7207708613:ℚ)/10000000000),((-11240682976701279553284094717966057:ℚ)/176242250000000000000000000000000000),((-4946286420620008416279797:ℚ)/18483200000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((6185046831:ℚ)/10000000000),((6488592931:ℚ)/10000000000),((47135327817:ℚ)/55300000000),((21129778793:ℚ)/21360000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1550243107:ℚ)/2500000000),((-76082235368706024476456709962826380979711641713166291943:ℚ)/1056952356250000000000000000000000000000000000000000000000),((-489811800015315028861562597:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((6422631147:ℚ)/10000000000),((6726222781:ℚ)/10000000000),((48798418029:ℚ)/57200000000),((21842668343:ℚ)/22120000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1410189619:ℚ)/2500000000),((-84281438615850173864821374939681714723841697566978676451:ℚ)/1169682800000000000000000000000000000000000000000000000000),((-484991221481004474669094493:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((3330104929:ℚ)/5000000000),((3422517261:ℚ)/5000000000),((25230734503:ℚ)/29075000000),((11099551783:ℚ)/11440000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1256446483:ℚ)/2500000000),((-11643228475193047845422803498589819063114916746694483537:ℚ)/153616967480468750000000000000000000000000000000000000000),((-120645843897274049890375557:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((1694749321:ℚ)/2500000000),((1740961069:ℚ)/2500000000),((12823245247:ℚ)/14775000000),((5638883207:ℚ)/5815000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4691048619:ℚ)/10000000000),((-42420353982401082655651913733220466327938536944378473:ℚ)/559963842773437500000000000000000000000000000000000000),((-30010833570025573152457557:ℚ)/115520000000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((3448891753:ℚ)/5000000000),((3511624219:ℚ)/5000000000),((26062242271:ℚ)/29787500000),((11366872657:ℚ)/11820000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((2166286071:ℚ)/5000000000),((-38432289367975558779976643824982007030132921542423092723:ℚ)/495568208752441406250000000000000000000000000000000000000),((-119742388252396610957014293:ℚ)/462080000000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((869647023:ℚ)/1250000000),((3541326069:ℚ)/5000000000),((6567529161:ℚ)/7506250000),((11455978207:ℚ)/11915000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2071256667:ℚ)/5000000000),((-51226000674406601791842125540637728383394142525843999:ℚ)/660829010391235351562500000000000000000000000000000000),((-7465071783193509537755333:ℚ)/28880000000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((7016568581:ℚ)/10000000000),((7142055387:ℚ)/10000000000),((52955980067:ℚ)/60525000000),((23090166161:ℚ)/24020000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((197192941:ℚ)/500000000),((-80531209373365377323771983222530155743593691461576290831:ℚ)/1039311361889648437500000000000000000000000000000000000000),((-476559654810984076174209597:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((3537980353:ℚ)/5000000000),((1800364549:ℚ)/2500000000),((26685862471:ℚ)/30500000000),((5817093647:ℚ)/6052500000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((933808391:ℚ)/2500000000),((-41204533399750141196191502508792075400267110147037902667:ℚ)/531986718750000000000000000000000000000000000000000000000),((-118838683711518341684807493:ℚ)/462080000000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((1783838141:ℚ)/2500000000),((290434423:ℚ)/400000000),((13446866987:ℚ)/15368750000),((937863269:ℚ)/976000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((1757429279:ℚ)/5000000000),((-109787735728563687231888285710113875425996595002687773:ℚ)/1417998178386688232421875000000000000000000000000000000),((-29634364626660482043096237:ℚ)/115520000000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((7194744161:ℚ)/10000000000),((3660131267:ℚ)/5000000000),((54203209127:ℚ)/61950000000),((11812393801:ℚ)/12295000000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((1640181177:ℚ)/5000000000),((-115006966196201800283589112046138695616505761675454365153:ℚ)/1485949155468750000000000000000000000000000000000000000000),((-472944952149407107388221317:ℚ)/1848320000000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((453383469:ℚ)/625000000),((743906523:ℚ)/1000000000),((3413684283:ℚ)/3931250000),((2398119569:ℚ)/2478000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((3028461917:ℚ)/10000000000),((-7181283960273651894465000181402915081521040187732637:ℚ)/94931865310668945312500000000000000000000000000000000),((-1838023306897760714665397:ℚ)/7220000000000000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((921614681:ℚ)/1250000000),((7676665983:ℚ)/10000000000),((6931302767:ℚ)/8100000000),((24693997949:ℚ)/25160000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2450684621:ℚ)/10000000000),((-8903486399352096749949110314219579249196768165116411:ℚ)/123018750000000000000000000000000000000000000000000000),((-7301075009212086698810997:ℚ)/28880000000000000000000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((3805239263:ℚ)/5000000000),((4788649819:ℚ)/5000000000),((28556674841:ℚ)/40000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-3035547861394741119459022422513327909742039819512157517:ℚ)/75000000000000000000000000000000000000000000000000000000),((-32359683:ℚ)/128000000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((2377715669:ℚ)/2500000000),((6689021671:ℚ)/5000000000),((17604009683:ℚ)/27600000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-124515693609358541008109177979388639:ℚ)/5256144000000000000000000000000000000),((-32359683:ℚ)/128000000)⟩
theorem valid14 : Valid source14 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source14 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source14 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC31
#check @N11Formalization.C450Source14GroupedC31.bound
#print axioms N11Formalization.C450Source14GroupedC31.valid0
#print axioms N11Formalization.C450Source14GroupedC31.valid1
#print axioms N11Formalization.C450Source14GroupedC31.valid2
#print axioms N11Formalization.C450Source14GroupedC31.valid3
#print axioms N11Formalization.C450Source14GroupedC31.valid4
#print axioms N11Formalization.C450Source14GroupedC31.valid5
#print axioms N11Formalization.C450Source14GroupedC31.valid6
#print axioms N11Formalization.C450Source14GroupedC31.valid7
#print axioms N11Formalization.C450Source14GroupedC31.valid8
#print axioms N11Formalization.C450Source14GroupedC31.valid9
#print axioms N11Formalization.C450Source14GroupedC31.valid10
#print axioms N11Formalization.C450Source14GroupedC31.valid11
#print axioms N11Formalization.C450Source14GroupedC31.valid12
#print axioms N11Formalization.C450Source14GroupedC31.valid13
#print axioms N11Formalization.C450Source14GroupedC31.valid14
#print axioms N11Formalization.C450Source14GroupedC31.bound
#print axioms N11Formalization.C450Source14GroupedC31.endpoint_checks
