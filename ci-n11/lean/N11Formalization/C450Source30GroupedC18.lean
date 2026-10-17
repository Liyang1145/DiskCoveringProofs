import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/16),((1:ℚ)/8),((743405377:ℚ)/1250000000),((6269708691:ℚ)/10000000000),((2983405377:ℚ)/12875000000),((15549708691:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1680185323:ℚ)/2500000000),((-1258916031517093766762675200779781280727820236446972883:ℚ)/13338952636718750000000000000000000000000000000000000000),((-308706426370263450922287977:ℚ)/1108992000000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((1237756981:ℚ)/2000000000),((6510738943:ℚ)/10000000000),((1607252327:ℚ)/7120000000),((15790738943:ℚ)/51500000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((3096251731:ℚ)/5000000000),((-51104302140006487503573843052723223915089296366697573:ℚ)/563975200000000000000000000000000000000000000000000000),((-105623877220205646292752811:ℚ)/369664000000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((6430032317:ℚ)/10000000000),((3315579767:ℚ)/5000000000),((24350032317:ℚ)/108700000000),((7955579767:ℚ)/26700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((140562929:ℚ)/250000000),((-719788639340190498081813127869250816906256150465959895703:ℚ)/8027284393750000000000000000000000000000000000000000000000),((-27220693617332888825913371:ℚ)/92416000000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((6550555543:ℚ)/10000000000),((421970097:ℚ)/625000000),((3495793649:ℚ)/15800000000),((1001970097:ℚ)/3396875000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((5317615641:ℚ)/10000000000),((-33882035522957966936427111491749793522412913902447811:ℚ)/385186718750000000000000000000000000000000000000000000),((-1291572603717928136198153:ℚ)/4332000000000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((6671016521:ℚ)/10000000000),((1717957011:ℚ)/2500000000),((2732335169:ℚ)/12500000000),((4037957011:ℚ)/13825000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1249046601:ℚ)/2500000000),((-4116542872657935812159687839821186865434665058668899:ℚ)/47683715820312500000000000000000000000000000000000000),((-20912704371848072886810857:ℚ)/69312000000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((3395709247:ℚ)/5000000000),((6992081849:ℚ)/10000000000),((12355709247:ℚ)/57200000000),((5424027283:ℚ)/18750000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4654767099:ℚ)/10000000000),((-99149003367422449207492144583197307132549440598693987613:ℚ)/1169682800000000000000000000000000000000000000000000000000),((-112843509507936137129518139:ℚ)/369664000000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((6911764483:ℚ)/10000000000),((7112285611:ℚ)/10000000000),((24831764483:ℚ)/116300000000),((1260945047:ℚ)/4400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((134017019:ℚ)/312500000),((-818618974721889555278215908636585219564055702059042581713:ℚ)/9831485918750000000000000000000000000000000000000000000000),((-114141502215810316622662419:ℚ)/369664000000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((7032057303:ℚ)/10000000000),((7232441803:ℚ)/10000000000),((24952057303:ℚ)/118200000000),((16512441803:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3890476899:ℚ)/10000000000),((-23459111123739031095444641309609127886607516419399390133:ℚ)/286701487500000000000000000000000000000000000000000000000),((-115428446262270337915405651:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((111754681:ℚ)/156250000),((934077571:ℚ)/1250000000),((391754681:ℚ)/1906250000),((698025857:ℚ)/2462500000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((431188649:ℚ)/1250000000),((-3396528182949120784766506785737830688635771530223411:ℚ)/43293190002441406250000000000000000000000000000000000),((-1813445292585396497642499:ℚ)/5776000000000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((3696321101:ℚ)/5000000000),((7952499613:ℚ)/10000000000),((12656321101:ℚ)/64800000000),((17232499613:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((2341320151:ℚ)/10000000000),((-507205520637027621575676137913862149942244802165307277:ℚ)/6998400000000000000000000000000000000000000000000000000),((-19602464551110251:ℚ)/60800000000000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((1574563843:ℚ)/2000000000),((9867328617:ℚ)/10000000000),((5158563843:ℚ)/32000000000),((19147328617:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-10973395007118782534092142932206452410139244071697987537:ℚ)/204800000000000000000000000000000000000000000000000000000),((-42408629:ℚ)/128000000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((9788550471:ℚ)/10000000000),((42764543:ℚ)/31250000),((27708550471:ℚ)/220800000000),((71764543:ℚ)/250000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-59262183260813153983988782500453788575862626978275227509:ℚ)/1868851200000000000000000000000000000000000000000000000000),((-42408629:ℚ)/128000000)⟩
theorem valid11 : Valid source30 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC18
#check @N11Formalization.C450Source30GroupedC18.bound
#print axioms N11Formalization.C450Source30GroupedC18.valid0
#print axioms N11Formalization.C450Source30GroupedC18.valid1
#print axioms N11Formalization.C450Source30GroupedC18.valid2
#print axioms N11Formalization.C450Source30GroupedC18.valid3
#print axioms N11Formalization.C450Source30GroupedC18.valid4
#print axioms N11Formalization.C450Source30GroupedC18.valid5
#print axioms N11Formalization.C450Source30GroupedC18.valid6
#print axioms N11Formalization.C450Source30GroupedC18.valid7
#print axioms N11Formalization.C450Source30GroupedC18.valid8
#print axioms N11Formalization.C450Source30GroupedC18.valid9
#print axioms N11Formalization.C450Source30GroupedC18.valid10
#print axioms N11Formalization.C450Source30GroupedC18.valid11
#print axioms N11Formalization.C450Source30GroupedC18.bound
#print axioms N11Formalization.C450Source30GroupedC18.endpoint_checks
