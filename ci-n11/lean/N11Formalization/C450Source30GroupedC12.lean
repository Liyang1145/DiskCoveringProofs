import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((3192212311:ℚ)/5000000000),((1676248153:ℚ)/2500000000),((-780248153:ℚ)/4960000000),((-872212311:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5734101243:ℚ)/10000000000),((1296823262171115455544949084597892839:ℚ)/10439934976000000000000000000000000000),((-462870226399413842152953:ℚ)/11552000000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((3312751417:ℚ)/5000000000),((13650977:ℚ)/20000000),((-6482977:ℚ)/41200000),((-992751417:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2559895081:ℚ)/5000000000),((231026365985862564342417305662619988015780275804123:ℚ)/1878809193010937500000000000000000000000000000000000),((-628635249789027858546777:ℚ)/11552000000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((53967541:ℚ)/80000000),((6885712431:ℚ)/10000000000),((-3301712431:ℚ)/20980000000),((-16847541:ℚ)/211700000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((598294823:ℚ)/1250000000),((433702975052122272758189657755760644007931001966721208586973:ℚ)/3543360380202850000000000000000000000000000000000000000000000),((-182366980481313631233:ℚ)/2957312000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((212691853:ℚ)/312500000),((6945920941:ℚ)/10000000000),((-3361920941:ℚ)/21170000000),((-22563951:ℚ)/278125000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((4503346:ℚ)/9765625),((14432321753410683547506020524252404443987790209906723778439:ℚ)/117425552797770312500000000000000000000000000000000000000000),((-2947081624112243952987:ℚ)/45125000000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/16),((-1:ℚ)/4),((6866321049:ℚ)/10000000000),((7006114447:ℚ)/10000000000),((-3422114447:ℚ)/21360000000),((-2226321049:ℚ)/26937500000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4430151159:ℚ)/10000000000),((155143228174615222897152934565702318461116287387048324529373:ℚ)/1257175165526400000000000000000000000000000000000000000000000),((-9560132115546488987185579:ℚ)/138624000000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((6926488291:ℚ)/10000000000),((1413258671:ℚ)/2000000000),((-696458671:ℚ)/4310000000),((-2286488291:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4241714753:ℚ)/10000000000),((73255432635815796074777116684582741981139493400404510893789:ℚ)/591249676330493750000000000000000000000000000000000000000000),((-3356182128712777971953233:ℚ)/46208000000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((1746660353:ℚ)/2500000000),((7126458053:ℚ)/10000000000),((-3542458053:ℚ)/21740000000),((-195553451:ℚ)/2284375000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2022555507:ℚ)/5000000000),((266774368882140608896827904594377947963706563959474140537807:ℚ)/2144733857964321875000000000000000000000000000000000000000000),((-220389157165774145219737:ℚ)/2888000000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((1761695197:ℚ)/2500000000),((7186608919:ℚ)/10000000000),((-3602608919:ℚ)/21930000000),((-601695197:ℚ)/6912500000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3839079793:ℚ)/10000000000),((382586800868383452496639040295991457410071902547428175911:ℚ)/3063982557168750000000000000000000000000000000000000000000),((-231052781260789140330337:ℚ)/2888000000000000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((3553453391:ℚ)/5000000000),((7306870587:ℚ)/10000000000),((-3722870587:ℚ)/22120000000),((-1233453391:ℚ)/14062500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((905501713:ℚ)/2500000000),((33086819945115006040255072918550439451110809837692868213:ℚ)/260916238800000000000000000000000000000000000000000000000),((-967009175194413606965833:ℚ)/11552000000000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((7227120017:ℚ)/10000000000),((928385139:ℚ)/1250000000),((-480385139:ℚ)/2812500000),((-2587120017:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3145463017:ℚ)/10000000000),((498117769225836258760290330728002123603588017526619209:ℚ)/3900337219238281250000000000000000000000000000000000000),((-4212146114136647688239977:ℚ)/46208000000000000000000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((114801309:ℚ)/156250000),((7667358831:ℚ)/10000000000),((-4083358831:ℚ)/22880000000),((-42301309:ℚ)/461718750),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((103441687:ℚ)/400000000),((95446525800338032071314776062428812005058728858561527277901:ℚ)/726307516563200000000000000000000000000000000000000000000000),((-1669394261617056075137:ℚ)/16921875000000000000000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((1896868157:ℚ)/2500000000),((1581492131:ℚ)/2000000000),((-864692131:ℚ)/4728000000),((-736868157:ℚ)/7625000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((71780731:ℚ)/1250000000),((36327789258218219241004657412521105656797573743822971281:ℚ)/273104956156800000000000000000000000000000000000000000000),((-328644583233597783495457:ℚ)/2888000000000000000000000)⟩
theorem valid11 : Valid source30 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source30 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((7827491303:ℚ)/10000000000),((8387199763:ℚ)/10000000000),((-4803199763:ℚ)/24400000000),((-1062497101:ℚ)/10800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((771034581354204457768952188198069368045140036054592025019:ℚ)/5515638300000000000000000000000000000000000000000000000000),((-7333903:ℚ)/64000000)⟩
theorem valid12 : Valid source30 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((8307079167:ℚ)/10000000000),((1287700613:ℚ)/1250000000),((-839700613:ℚ)/3240000000),((-3667079167:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((84285478504584011808122445321205007711721473105621:ℚ)/492075000000000000000000000000000000000000000000000),((-7333903:ℚ)/64000000)⟩
theorem valid13 : Valid source30 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((10221026101:ℚ)/10000000000),((1411843713:ℚ)/1000000000),((-1053443713:ℚ)/3200000000),((-5581026101:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2795654987096484674724616508049313907:ℚ)/13000704000000000000000000000000000000),((-7333903:ℚ)/64000000)⟩
theorem valid14 : Valid source30 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source30 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source30 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source30 nn0 nn1 Qcell ((2117:ℚ)/3200) ((2193:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source30 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source30 nn0 nn1 Qcell ((2193:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source30 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC12
#check @N11Formalization.C450Source30GroupedC12.bound
#print axioms N11Formalization.C450Source30GroupedC12.valid0
#print axioms N11Formalization.C450Source30GroupedC12.valid1
#print axioms N11Formalization.C450Source30GroupedC12.valid2
#print axioms N11Formalization.C450Source30GroupedC12.valid3
#print axioms N11Formalization.C450Source30GroupedC12.valid4
#print axioms N11Formalization.C450Source30GroupedC12.valid5
#print axioms N11Formalization.C450Source30GroupedC12.valid6
#print axioms N11Formalization.C450Source30GroupedC12.valid7
#print axioms N11Formalization.C450Source30GroupedC12.valid8
#print axioms N11Formalization.C450Source30GroupedC12.valid9
#print axioms N11Formalization.C450Source30GroupedC12.valid10
#print axioms N11Formalization.C450Source30GroupedC12.valid11
#print axioms N11Formalization.C450Source30GroupedC12.valid12
#print axioms N11Formalization.C450Source30GroupedC12.valid13
#print axioms N11Formalization.C450Source30GroupedC12.valid14
#print axioms N11Formalization.C450Source30GroupedC12.bound
#print axioms N11Formalization.C450Source30GroupedC12.endpoint_checks
