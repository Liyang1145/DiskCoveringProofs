import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((2899999999:ℚ)/5000000000),((6336324337:ℚ)/10000000000),((3091999999:ℚ)/3560000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3513052179:ℚ)/5000000000),((-3897728722641079805915187740943353275309591809904399:ℚ)/70496900000000000000000000000000000000000000000000000),((-1540193056165077654467257:ℚ)/7220000000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((6274999997:ℚ)/10000000000),((6573864737:ℚ)/10000000000),((19976999991:ℚ)/22120000000),(1:ℚ),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5994289947:ℚ)/10000000000),((-65127381574722527124474987531564229092994659011921799:ℚ)/1056952356250000000000000000000000000000000000000000000),((-1523815625381154252556057:ℚ)/7220000000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((15:ℚ)/16),(1:ℚ),((3256249999:ℚ)/5000000000),((3346316957:ℚ)/5000000000),((3448249999:ℚ)/3750000000),(1:ℚ),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((338472201:ℚ)/625000000),((-249827612934266004152052088925899069157468463609757:ℚ)/3862380981445312500000000000000000000000000000000000),((-378902721337110466944097:ℚ)/1805000000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3315624999:ℚ)/5000000000),((6811402453:ℚ)/10000000000),((10522874997:ℚ)/11440000000),(1:ℚ),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1020866617:ℚ)/2000000000),((-604796588119104282558501783173119892147005535269262173:ℚ)/9357462400000000000000000000000000000000000000000000000),((-1507395459422809909988177:ℚ)/7220000000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3374999999:ℚ)/5000000000),((6930170387:ℚ)/10000000000),((10700999997:ℚ)/11630000000),(1:ℚ),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4774754179:ℚ)/10000000000),((-635006055441866333471365947354968335463913975610229717:ℚ)/9831485918750000000000000000000000000000000000000000000),((-1499169345490036158777857:ℚ)/7220000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((15:ℚ)/16),(1:ℚ),((3434374999:ℚ)/5000000000),((1397910827:ℚ)/2000000000),((10879124997:ℚ)/11725000000),(1:ℚ),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((4422689627:ℚ)/10000000000),((-665313497931469094643668298205686482876246118837229917:ℚ)/10074385644531250000000000000000000000000000000000000000),((-59802091201042485632337:ℚ)/288800000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((6928124997:ℚ)/10000000000),((7048937743:ℚ)/10000000000),((7312124997:ℚ)/7880000000),(1:ℚ),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2118239557:ℚ)/5000000000),((-50464986235946074952849816638287793144255977410281013:ℚ)/764537300000000000000000000000000000000000000000000000),((-1490932541840357828416697:ℚ)/7220000000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3493749999:ℚ)/5000000000),((3554160607:ℚ)/5000000000),((11057249997:ℚ)/11915000000),(1:ℚ),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((505279951:ℚ)/1250000000),((-697507887547217049612464033303374396639185465617410317:ℚ)/10572121786718750000000000000000000000000000000000000000),((-371702532685891701919897:ℚ)/1805000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3523437499:ℚ)/5000000000),((7167704551:ℚ)/10000000000),((11146312497:ℚ)/12010000000),(1:ℚ),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1919374409:ℚ)/5000000000),((-178501968958433197457462887386961065327087408066580353:ℚ)/2706755626562500000000000000000000000000000000000000000),((-1482685046545790568887753:ℚ)/7220000000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((7106249997:ℚ)/10000000000),((7227087757:ℚ)/10000000000),((2496749999:ℚ)/2690000000),(1:ℚ),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((362444499:ℚ)/1000000000),((-6014649785799458259018032528789181898892389025100917:ℚ)/91242698437500000000000000000000000000000000000000000),((-1478557289056588509637697:ℚ)/7220000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3582812499:ℚ)/5000000000),((1457294167:ℚ)/2000000000),((11324437497:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1698639171:ℚ)/5000000000),((-747826789086304505564155288942387188307428749558264193:ℚ)/11349050000000000000000000000000000000000000000000000000),((-163371397017726087297:ℚ)/800000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((7224999997:ℚ)/10000000000),((1836463447:ℚ)/2500000000),((22826999991:ℚ)/24590000000),(1:ℚ),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((197154177:ℚ)/625000000),((-382575543925478604051726183401170420792870757366944399:ℚ)/5808120538671875000000000000000000000000000000000000000),((-91893359589964629671977:ℚ)/451250000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3642187499:ℚ)/5000000000),((7405236619:ℚ)/10000000000),((3834187499:ℚ)/4130000000),(1:ℚ),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((2892067893:ℚ)/10000000000),((-28990946316778672393914081831447278700307136742718931:ℚ)/440281231250000000000000000000000000000000000000000000),((-1466157974927890057708433:ℚ)/7220000000000000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3671874999:ℚ)/5000000000),((3762000963:ℚ)/5000000000),((11591624997:ℚ)/12580000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((65104053:ℚ)/250000000),((-200505744579413848310362846351973800832602760964962757:ℚ)/3110727362500000000000000000000000000000000000000000000),((-1093408796704186999871971:ℚ)/5415000000000000000000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((3731249999:ℚ)/5000000000),((1552306239:ℚ)/2000000000),((3923249999:ℚ)/4320000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((476273613:ℚ)/2500000000),((-10391180099211088247762681764326960529021510268482973:ℚ)/167961600000000000000000000000000000000000000000000000),((-1609501:ℚ)/8000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((15:ℚ)/16),(1:ℚ),((3849999999:ℚ)/5000000000),((2415428821:ℚ)/2500000000),((12125999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-58649926050343650321276012800182091919617007298699413:ℚ)/1600000000000000000000000000000000000000000000000000000),((-1609501:ℚ)/8000000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4799999999:ℚ)/5000000000),((13461931377:ℚ)/10000000000),((4991999999:ℚ)/7360000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-2409667532211964028124288767991877:ℚ)/99672064000000000000000000000000000),((-1609501:ℚ)/8000000)⟩
theorem valid16 : Valid source11 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2383:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((2383:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source11 nn0 nn1 Qcell ((2421:ℚ)/3200) ((2459:ℚ)/3200) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2459:ℚ)/3200) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source11 nn0 nn1 Qcell ((2459:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source11 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source11 nn0 nn1 Qcell ((2459:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC32
#check @N11Formalization.C450Source11GroupedC32.bound
#print axioms N11Formalization.C450Source11GroupedC32.valid0
#print axioms N11Formalization.C450Source11GroupedC32.valid1
#print axioms N11Formalization.C450Source11GroupedC32.valid2
#print axioms N11Formalization.C450Source11GroupedC32.valid3
#print axioms N11Formalization.C450Source11GroupedC32.valid4
#print axioms N11Formalization.C450Source11GroupedC32.valid5
#print axioms N11Formalization.C450Source11GroupedC32.valid6
#print axioms N11Formalization.C450Source11GroupedC32.valid7
#print axioms N11Formalization.C450Source11GroupedC32.valid8
#print axioms N11Formalization.C450Source11GroupedC32.valid9
#print axioms N11Formalization.C450Source11GroupedC32.valid10
#print axioms N11Formalization.C450Source11GroupedC32.valid11
#print axioms N11Formalization.C450Source11GroupedC32.valid12
#print axioms N11Formalization.C450Source11GroupedC32.valid13
#print axioms N11Formalization.C450Source11GroupedC32.valid14
#print axioms N11Formalization.C450Source11GroupedC32.valid15
#print axioms N11Formalization.C450Source11GroupedC32.valid16
#print axioms N11Formalization.C450Source11GroupedC32.bound
#print axioms N11Formalization.C450Source11GroupedC32.endpoint_checks
