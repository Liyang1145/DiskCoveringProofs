import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((3212799373:ℚ)/5000000000),((6735688691:ℚ)/10000000000),((-12847066073:ℚ)/49600000000),((-1676799373:ℚ)/10300000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5633450701:ℚ)/10000000000),((47850156191792857880294948975658208531428433128741154697:ℚ)/211715856250000000000000000000000000000000000000000000000),((-4865521863564589304199711:ℚ)/147865600000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((3332702119:ℚ)/5000000000),((1371113761:ℚ)/2000000000),((-2641341283:ℚ)/10300000000),((-1796702119:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((100231569:ℚ)/200000000),((41102887496019249941443938100657384746378798475673620483:ℚ)/185773479448437500000000000000000000000000000000000000000),((-6714002704510392735365399:ℚ)/147865600000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((1696310869:ℚ)/2500000000),((6975408153:ℚ)/10000000000),((-13566224459:ℚ)/52450000000),((-928310869:ℚ)/5340000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((2336418261:ℚ)/5000000000),((2041458656549120463238684748780672737100186834963074453:ℚ)/9243906012500000000000000000000000000000000000000000000),((-1911257447097108615120399:ℚ)/36966400000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/8),((-5:ℚ)/16),((6905043443:ℚ)/10000000000),((7035313227:ℚ)/10000000000),((-13745939681:ℚ)/53400000000),((-3833043443:ℚ)/21550000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4309762471:ℚ)/10000000000),((4755912181830897374472731121453555546534345369076923393:ℚ)/21745624386596679687500000000000000000000000000000000000),((-34322393920160032003093791:ℚ)/591462400000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((87061617:ℚ)/125000000),((7095208913:ℚ)/10000000000),((-13925626739:ℚ)/53875000000),((-48661617:ℚ)/271750000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4117094671:ℚ)/10000000000),((11814866030519172543857445005950340873015904118228973:ℚ)/54058743339160156250000000000000000000000000000000000),((-16968918040095975787253:ℚ)/277248000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((7024806233:ℚ)/10000000000),((7155095459:ℚ)/10000000000),((-14105286377:ℚ)/54350000000),((-3952806233:ℚ)/21930000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((978888413:ℚ)/2500000000),((434714377456798012993909127137172781023655900611006334461:ℚ)/1990320222735937500000000000000000000000000000000000000000),((-38082881975555142716176151:ℚ)/591462400000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((7084674301:ℚ)/10000000000),((3607486553:ℚ)/5000000000),((-166103713:ℚ)/637500000),((-4012674301:ℚ)/22120000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3703686109:ℚ)/10000000000),((3922114008364034989956103218800125648411636530589876343:ℚ)/17968190056250000000000000000000000000000000000000000000),((-39969969739206334697159359:ℚ)/591462400000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((1428906759:ℚ)/2000000000),((1818710521:ℚ)/2500000000),((-3616131563:ℚ)/13825000000),((-814506759:ℚ)/4462000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((869900243:ℚ)/2500000000),((4186398863607897777108286354007310443184878378565374653:ℚ)/19189950913196875000000000000000000000000000000000000000),((-5023395233996337923164037:ℚ)/70975488000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((7204384937:ℚ)/10000000000),((7334702617:ℚ)/10000000000),((-14644107851:ℚ)/55775000000),((-4132384937:ℚ)/22500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3240759271:ℚ)/10000000000),((135275832244474634450602255167611529016861678640367003253:ℚ)/620421981811523437500000000000000000000000000000000000000),((-43757858570820838552145271:ℚ)/591462400000000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((3632113971:ℚ)/5000000000),((3727199601:ℚ)/5000000000),((-7501598803:ℚ)/28125000000),((-2096113971:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2983613313:ℚ)/10000000000),((6164399170314157636678076776081287613113319006890896203:ℚ)/28072387200000000000000000000000000000000000000000000000),((-34244002060634295553038557:ℚ)/443596800000000000000000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((1476778073:ℚ)/2000000000),((7693700041:ℚ)/10000000000),((-15721100123:ℚ)/57200000000),((-862378073:ℚ)/4728000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1195225343:ℚ)/5000000000),((583992474200068473249467838819581665120881344060170189:ℚ)/2623892013600000000000000000000000000000000000000000000),((-1978961888648814535391511:ℚ)/23658496000000000000000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((7623126249:ℚ)/10000000000),((7932887497:ℚ)/10000000000),((-16438662491:ℚ)/59100000000),((-4551126249:ℚ)/24400000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((3971824354542827870302428049151754772661070279761413346743:ℚ)/17886102800000000000000000000000000000000000000000000000000),((-97668973:ℚ)/1024000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((7862252881:ℚ)/10000000000),((4205481339:ℚ)/5000000000),((-8936444017:ℚ)/30500000000),((-4790252881:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((167795891272457469948955135005297863790476342037293843119:ℚ)/737687347200000000000000000000000000000000000000000000000),((-97668973:ℚ)/1024000000)⟩
theorem valid12 : Valid source25 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((4170108659:ℚ)/5000000000),((5160160641:ℚ)/5000000000),((-11800481923:ℚ)/32400000000),((-2634108659:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((177325311054923502699202671858538402885183936299414428483:ℚ)/691200000000000000000000000000000000000000000000000000000),((-97668973:ℚ)/1024000000)⟩
theorem valid13 : Valid source25 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((10249239617:ℚ)/10000000000),((14131274453:ℚ)/10000000000),((-35033823359:ℚ)/80000000000),((-7177239617:ℚ)/44160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((39520063870450972914853799412851589385092133148407686803:ℚ)/134557286400000000000000000000000000000000000000000000000),((-97668973:ℚ)/1024000000)⟩
theorem valid14 : Valid source25 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC11
#check @N11Formalization.C450Source25GroupedC11.bound
#print axioms N11Formalization.C450Source25GroupedC11.valid0
#print axioms N11Formalization.C450Source25GroupedC11.valid1
#print axioms N11Formalization.C450Source25GroupedC11.valid2
#print axioms N11Formalization.C450Source25GroupedC11.valid3
#print axioms N11Formalization.C450Source25GroupedC11.valid4
#print axioms N11Formalization.C450Source25GroupedC11.valid5
#print axioms N11Formalization.C450Source25GroupedC11.valid6
#print axioms N11Formalization.C450Source25GroupedC11.valid7
#print axioms N11Formalization.C450Source25GroupedC11.valid8
#print axioms N11Formalization.C450Source25GroupedC11.valid9
#print axioms N11Formalization.C450Source25GroupedC11.valid10
#print axioms N11Formalization.C450Source25GroupedC11.valid11
#print axioms N11Formalization.C450Source25GroupedC11.valid12
#print axioms N11Formalization.C450Source25GroupedC11.valid13
#print axioms N11Formalization.C450Source25GroupedC11.valid14
#print axioms N11Formalization.C450Source25GroupedC11.bound
#print axioms N11Formalization.C450Source25GroupedC11.endpoint_checks
