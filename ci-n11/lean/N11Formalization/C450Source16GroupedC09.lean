import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((1606129141:ℚ)/2500000000),((335824743:ℚ)/500000000),((-279824743:ℚ)/620000000),((-8842903987:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((176128643:ℚ)/312500000),((7430231113552832483606292159040150347660769983861751993:ℚ)/124052259521484375000000000000000000000000000000000000000),((7716884190112056765603179:ℚ)/48640000000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((6662774631:ℚ)/10000000000),((6835626527:ℚ)/10000000000),((-5715626527:ℚ)/12875000000),((-37039422417:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2509387727:ℚ)/5000000000),((134956758236469413499806776495382066629022463102541684057:ℚ)/2322168493105468750000000000000000000000000000000000000000),((19173941846338321242820163:ℚ)/122880000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((271275319:ℚ)/400000000),((6954744551:ℚ)/10000000000),((-5834744551:ℚ)/13112500000),((-1514927233:ℚ)/4272000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((187305717:ℚ)/400000000),((92750527292701346960774566650454406131916927861492351:ℚ)/1597346958960000000000000000000000000000000000000000000),((192663013697891113418099:ℚ)/1245184000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((6900978513:ℚ)/10000000000),((7014298673:ℚ)/10000000000),((-5894298673:ℚ)/13350000000),((-38706849591:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4322547787:ℚ)/10000000000),((1945358535851118600903517546864325047160116190308427113:ℚ)/33977538104057312011718750000000000000000000000000000000),((358175402854183626914182313:ℚ)/2334720000000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((6960521693:ℚ)/10000000000),((7073849651:ℚ)/10000000000),((-5953849651:ℚ)/13468750000),((-39123651851:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2065781607:ℚ)/5000000000),((2475489524247165476624212804365607699349483116311874709987:ℚ)/43246994671328125000000000000000000000000000000000000000000),((6256829347127777068539289:ℚ)/40960000000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7020061921:ℚ)/10000000000),((3566698783:ℚ)/5000000000),((-3006698783:ℚ)/6793750000),((-39540433447:ℚ)/109650000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((6143561:ℚ)/15625000),((1847441421177473698871162974420350713418886679547454861:ℚ)/32282443059082031250000000000000000000000000000000000000),((118367212056071811589124419:ℚ)/778240000000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((3539799637:ℚ)/5000000000),((3596471249:ℚ)/5000000000),((-1012157083:ℚ)/2284375000),((-19978597459:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3722091179:ℚ)/10000000000),((25901750318901278982868441208354859307619368156595094461:ℚ)/452714163526611328125000000000000000000000000000000000000),((29463540936981457842176171:ℚ)/194560000000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((3569566913:ℚ)/5000000000),((1813121131:ℚ)/2500000000),((-1533121131:ℚ)/3456250000),((-20186968391:ℚ)/55775000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((54693423:ℚ)/156250000),((26799163444450573615403399657806511387473812283387114609:ℚ)/468504660966720581054687500000000000000000000000000000000),((29335153027186983445386371:ℚ)/194560000000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/2),((-7:ℚ)/16),((7198665651:ℚ)/10000000000),((1828005929:ℚ)/2500000000),((-1548005929:ℚ)/3485937500),((-13596886519:ℚ)/37500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3264309273:ℚ)/10000000000),((6159929896177798547373430591963795988356907851342731269:ℚ)/107712149620056152343750000000000000000000000000000000000),((350479669721010618544779377:ℚ)/2334720000000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((56704647:ℚ)/78125000),((1842890037:ℚ)/2500000000),((-1562890037:ℚ)/3515625000),((-321932529:ℚ)/886328125),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((188156319:ℚ)/625000000),((93306327450262551637156195343084909309288403749:ℚ)/1631905014021322131156921386718750000000000000000),((21297362665235014945193:ℚ)/142500000000000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((731772139:ℚ)/1000000000),((58055421:ℚ)/78125000),((-394443368:ℚ)/886328125),((-4162404973:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2734013447:ℚ)/10000000000),((1167029738084507028434711796355571289096176819504099667:ℚ)/20415463640000000000000000000000000000000000000000000000),((60945753562263347609481:ℚ)/409600000000000000000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((1844311359:ℚ)/2500000000),((7550153557:ℚ)/10000000000),((-6430153557:ℚ)/14300000000),((-10510179513:ℚ)/29075000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2427101907:ℚ)/10000000000),((15881836332227632552525848407550598595766572662744918593:ℚ)/274590329371337890625000000000000000000000000000000000000),((21615255280173979982342537:ℚ)/145920000000000000000000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((3748143099:ℚ)/5000000000),((7669203233:ℚ)/10000000000),((-6549203233:ℚ)/14537500000),((-7145667231:ℚ)/19700000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((206743383:ℚ)/1250000000),((10037352187687326708045161208680514422675206578181153371:ℚ)/173663453105468750000000000000000000000000000000000000000),((85686527092075357157169377:ℚ)/583680000000000000000000000)⟩
theorem valid12 : Valid source16 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/2),((-7:ℚ)/16),((7615317579:ℚ)/10000000000),((3953637241:ℚ)/5000000000),((-3393637241:ℚ)/7387500000),((-43707223053:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((1650047049655623521625976469198927771274365145525952643783:ℚ)/27947035625000000000000000000000000000000000000000000000000),((149141163:ℚ)/1024000000)⟩
theorem valid13 : Valid source16 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((7853353959:ℚ)/10000000000),((4191658077:ℚ)/5000000000),((-3631658077:ℚ)/7625000000),((-15124492571:ℚ)/43200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((7847938703403010138068164739545152083712438273032331859:ℚ)/128070720000000000000000000000000000000000000000000000000),((149141163:ℚ)/1024000000)⟩
theorem valid14 : Valid source16 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((4164666033:ℚ)/5000000000),((5143245439:ℚ)/5000000000),((-4583245439:ℚ)/8100000000),((-24352662231:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((78263511742271611474838126111837373293439023212254960379:ℚ)/1080000000000000000000000000000000000000000000000000000000),((149141163:ℚ)/1024000000)⟩
theorem valid15 : Valid source16 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((25580783:ℚ)/25000000),((3522553481:ℚ)/2500000000),((-3242553481:ℚ)/5000000000),((-155065481:ℚ)/552000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((826437632370177485100854282491129604015678200661:ℚ)/9855270000000000000000000000000000000000000000000),((149141163:ℚ)/1024000000)⟩
theorem valid16 : Valid source16 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source16 nn0 nn1 Qcell ((1049:ℚ)/1600) ((431:ℚ)/640) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source16 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source16 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source16 nn0 nn1 Qcell ((431:ℚ)/640) ((2231:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source16 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source16 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source16 nn0 nn1 Qcell ((2231:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source16 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC09
#check @N11Formalization.C450Source16GroupedC09.bound
#print axioms N11Formalization.C450Source16GroupedC09.valid0
#print axioms N11Formalization.C450Source16GroupedC09.valid1
#print axioms N11Formalization.C450Source16GroupedC09.valid2
#print axioms N11Formalization.C450Source16GroupedC09.valid3
#print axioms N11Formalization.C450Source16GroupedC09.valid4
#print axioms N11Formalization.C450Source16GroupedC09.valid5
#print axioms N11Formalization.C450Source16GroupedC09.valid6
#print axioms N11Formalization.C450Source16GroupedC09.valid7
#print axioms N11Formalization.C450Source16GroupedC09.valid8
#print axioms N11Formalization.C450Source16GroupedC09.valid9
#print axioms N11Formalization.C450Source16GroupedC09.valid10
#print axioms N11Formalization.C450Source16GroupedC09.valid11
#print axioms N11Formalization.C450Source16GroupedC09.valid12
#print axioms N11Formalization.C450Source16GroupedC09.valid13
#print axioms N11Formalization.C450Source16GroupedC09.valid14
#print axioms N11Formalization.C450Source16GroupedC09.valid15
#print axioms N11Formalization.C450Source16GroupedC09.valid16
#print axioms N11Formalization.C450Source16GroupedC09.bound
#print axioms N11Formalization.C450Source16GroupedC09.endpoint_checks
