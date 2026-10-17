import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),(0:ℚ),((1:ℚ)/16),((1491149273:ℚ)/2500000000),((787589343:ℚ)/1250000000),((528:ℚ)/2575),((3507589343:ℚ)/12400000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((668398117:ℚ)/1000000000),((-38749518904852081243889604144628678033779:ℚ)/210022129400000000000000000000000000000000),((-3294155752431974120603201:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((3103888057:ℚ)/5000000000),((6421994557:ℚ)/10000000000),((1056:ℚ)/5245),((28181994557:ℚ)/103000000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((122986411:ℚ)/200000000),((-277024473266948529676351868831185791345391749:ℚ)/1530773470655125000000000000000000000000000000),((-219150797472850130159963601:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((6329206033:ℚ)/10000000000),((25559303:ℚ)/39062500),((88:ℚ)/445),((110559303:ℚ)/409765625),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((1173334521:ℚ)/2000000000),((-336078302973281888774051118509525521151:ℚ)/1893917462326660156250000000000000000000),((-1741292878465796867591367:ℚ)/7220000000000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((3225268733:ℚ)/5000000000),((6664280839:ℚ)/10000000000),((1056:ℚ)/5435),((28424280839:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((696462603:ℚ)/1250000000),((-212559303516880446862577965648556875123937633:ℚ)/1220815097911560000000000000000000000000000000),((-226601605416292093900716729:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),(0:ℚ),((1:ℚ)/16),((3285887899:ℚ)/5000000000),((6724799053:ℚ)/10000000000),((704:ℚ)/3655),((28484799053:ℚ)/108700000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((5262289119:ℚ)/10000000000),((-99565609499803646158139455366521791431720967:ℚ)/576927488563723750000000000000000000000000000),((-230730372655658848658077041:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((6632361627:ℚ)/10000000000),((6785297067:ℚ)/10000000000),((528:ℚ)/2765),((28545297067:ℚ)/109650000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2550669209:ℚ)/5000000000),((-1207334154160278804348869758226297778280617:ℚ)/7059926475476328125000000000000000000000000),((-232576133423492246318623361:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((3346463013:ℚ)/5000000000),((3453117309:ℚ)/5000000000),((352:ℚ)/1875),((2047588187:ℚ)/7900000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((493567771:ℚ)/1000000000),((-1457483492096109313394718131814813653:ℚ)/8679199218750000000000000000000000000),((-58494728065095540188593169:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((6813992791:ℚ)/10000000000),((3513548777:ℚ)/5000000000),((12:ℚ)/65),((14393548777:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1147037207:ℚ)/2500000000),((-95618169845289939153038223673425913217:ℚ)/579287109375000000000000000000000000000),((-59410116079862764936616121:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((6934980411:ℚ)/10000000000),((1817153617:ℚ)/2500000000),((176:ℚ)/985),((7257153617:ℚ)/28600000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((168579321:ℚ)/400000000),((-124768998274016746911483445373009268089729:ℚ)/781701162385000000000000000000000000000000),((-15022896991742996423398161:ℚ)/57760000000000000000000000)⟩
theorem valid8 : Valid source35 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((1794183509:ℚ)/2500000000),((234683599:ℚ)/312500000),((264:ℚ)/1525),((304894533:ℚ)/1231250000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1676568779:ℚ)/5000000000),((-2080449813863240554611400577651617221:ℚ)/13441323286437988281250000000000000000),((-483537243619280019771573:ℚ)/1805000000000000000000000)⟩
theorem valid9 : Valid source35 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source35 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((296728639:ℚ)/400000000),((3995860359:ℚ)/5000000000),((22:ℚ)/135),((14875860359:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1095785479:ℚ)/5000000000),((-99113860064289431619321404250996282557:ℚ)/678152250000000000000000000000000000000),((-431036119429227:ℚ)/1556480000000000)⟩
theorem valid10 : Valid source35 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((7900463353:ℚ)/10000000000),((1982499433:ℚ)/2000000000),((33:ℚ)/250),((2111499811:ℚ)/8640000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-3970695692864132188694344088170113743:ℚ)/32400000000000000000000000000000000000),((-36393219:ℚ)/128000000)⟩
theorem valid11 : Valid source35 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((9822453:ℚ)/10000000),((13736724503:ℚ)/10000000000),((11:ℚ)/115),((35496724503:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-3769329311728480822333006505010173435099:ℚ)/38934400000000000000000000000000000000000),((-36393219:ℚ)/128000000)⟩
theorem valid12 : Valid source35 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC17
#check @N11Formalization.C450Source35GroupedC17.bound
#print axioms N11Formalization.C450Source35GroupedC17.valid0
#print axioms N11Formalization.C450Source35GroupedC17.valid1
#print axioms N11Formalization.C450Source35GroupedC17.valid2
#print axioms N11Formalization.C450Source35GroupedC17.valid3
#print axioms N11Formalization.C450Source35GroupedC17.valid4
#print axioms N11Formalization.C450Source35GroupedC17.valid5
#print axioms N11Formalization.C450Source35GroupedC17.valid6
#print axioms N11Formalization.C450Source35GroupedC17.valid7
#print axioms N11Formalization.C450Source35GroupedC17.valid8
#print axioms N11Formalization.C450Source35GroupedC17.valid9
#print axioms N11Formalization.C450Source35GroupedC17.valid10
#print axioms N11Formalization.C450Source35GroupedC17.valid11
#print axioms N11Formalization.C450Source35GroupedC17.valid12
#print axioms N11Formalization.C450Source35GroupedC17.bound
#print axioms N11Formalization.C450Source35GroupedC17.endpoint_checks
