import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC16
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((-1:ℚ)/16),(0:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/16),(0:ℚ),((3019933773:ℚ)/5000000000),((6377776119:ℚ)/10000000000),((15382223881:ℚ)/103000000000),((7:ℚ)/31),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1630627889:ℚ)/2500000000),((-1717209096502607029886045122543873145729115651761361897136307:ℚ)/9844787315625000000000000000000000000000000000000000000000000),((-85865104693158369:ℚ)/486400000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((6283423129:ℚ)/10000000000),((3249603019:ℚ)/5000000000),((7630396981:ℚ)/52450000000),((112:ℚ)/515),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2987308371:ℚ)/5000000000),((-204042599786546191182840091101164210075433306473204589050029:ℚ)/1195916773949316406250000000000000000000000000000000000000000),((-180754151489379037:ℚ)/972800000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/16),(0:ℚ),((6405030369:ℚ)/10000000000),((6620537471:ℚ)/10000000000),((15139462529:ℚ)/106800000000),((224:ℚ)/1049),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((1420982141:ℚ)/2500000000),((-174683304387752673068880780963058336691030722714675542852940921:ℚ)/1047260599968150000000000000000000000000000000000000000000000000),((-185259803462354757:ℚ)/972800000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/16),(0:ℚ),((1305306477:ℚ)/2000000000),((3340583977:ℚ)/5000000000),((7539416023:ℚ)/53875000000),((56:ℚ)/267),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2689814367:ℚ)/5000000000),((-7486985905195034852773090498929781634329463860484565599069:ℚ)/45360013368916511535644531250000000000000000000000000000000),((-37952311359274881:ℚ)/194560000000000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((6587245753:ℚ)/10000000000),((6741775803:ℚ)/10000000000),((15018224197:ℚ)/108700000000),((448:ℚ)/2155),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5221620709:ℚ)/10000000000),((-121730265232985542836412538102608159889113317058370640938654717:ℚ)/745578188133696875000000000000000000000000000000000000000000000),((-192011038869277309:ℚ)/972800000000000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/16),(0:ℚ),((1329586989:ℚ)/2000000000),((212573801:ℚ)/312500000),((155808733:ℚ)/1142187500),((224:ℚ)/1087),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((126480371:ℚ)/250000000),((-222182910355351841161873375524495679356435766177744063577:ℚ)/1375502320679959654808044433593750000000000000000000000000),((-38851925040151617:ℚ)/194560000000000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((6708600617:ℚ)/10000000000),((6862926031:ℚ)/10000000000),((14897073969:ℚ)/110600000000),((448:ℚ)/2193),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((611495929:ℚ)/1250000000),((-5642017644531097886988236140247411168374735196938315880728609:ℚ)/35299632377381640625000000000000000000000000000000000000000000),((-10342491584009279:ℚ)/51200000000000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/16),(0:ℚ),((6769243401:ℚ)/10000000000),((6923469569:ℚ)/10000000000),((14836530431:ℚ)/111550000000),((16:ℚ)/79),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((2359678999:ℚ)/5000000000),((-267634270907405649255649166195716929011433259165537347030431:ℚ)/1691971118462670898437500000000000000000000000000000000000000),((-198754206971671053:ℚ)/972800000000000000)⟩
theorem valid7 : Valid source36 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/16),(0:ℚ),((6829863907:ℚ)/10000000000),((1745998199:ℚ)/2500000000),((3694001801:ℚ)/28125000000),((448:ℚ)/2231),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((227038461:ℚ)/500000000),((-634906208991374033362321386284428418742864585525021984037747:ℚ)/4055160472914576530456542968750000000000000000000000000000000),((-201000248428262671:ℚ)/972800000000000000)⟩
theorem valid8 : Valid source36 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source36 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source36 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/16),(0:ℚ),((3445231361:ℚ)/5000000000),((111015319:ℚ)/156250000),((228984681:ℚ)/1787500000),((224:ℚ)/1125),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1088864913:ℚ)/2500000000),((-221754442868097973194854376235619703910705177414861169:ℚ)/1445683392333984375000000000000000000000000000000000000),((-101622743107400933:ℚ)/486400000000000000)⟩
theorem valid9 : Valid source36 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((7011597533:ℚ)/10000000000),((7346734041:ℚ)/10000000000),((14413265959:ℚ)/118200000000),((28:ℚ)/143),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3960846931:ℚ)/10000000000),((-432369995285303677920755014407476970480085757592205219159471:ℚ)/2931379358943750000000000000000000000000000000000000000000000),((-207733634290345649:ℚ)/972800000000000000)⟩
theorem valid10 : Valid source36 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/16),(0:ℚ),((3626815277:ℚ)/5000000000),((379410799:ℚ)/500000000),((708589201:ℚ)/6100000000),((112:ℚ)/591),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((30306889:ℚ)/100000000),((-11750136574550546850397320302433354470925508284141332126123:ℚ)/82583490271875000000000000000000000000000000000000000000000),((-108350582086281281:ℚ)/486400000000000000)⟩
theorem valid11 : Valid source36 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source36 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/16),(0:ℚ),((7495373571:ℚ)/10000000000),((4035231679:ℚ)/5000000000),((6844768321:ℚ)/64800000000),((56:ℚ)/305),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((830612383:ℚ)/5000000000),((-140240949015528743151415872011444731920418799968885879969043:ℚ)/1054662379200000000000000000000000000000000000000000000000000),((-225657949159206063:ℚ)/972800000000000000)⟩
theorem valid12 : Valid source36 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/16),(0:ℚ),((249315469:ℚ)/312500000),((1998490601:ℚ)/2000000000),((2353509399:ℚ)/32000000000),((14:ℚ)/81),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-24077056444901117218349457800883538516707442681254098138677:ℚ)/223948800000000000000000000000000000000000000000000000000000),((-30201901:ℚ)/128000000)⟩
theorem valid13 : Valid source36 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/16),(0:ℚ),((9901515033:ℚ)/10000000000),((13818085053:ℚ)/10000000000),((7941914947:ℚ)/220800000000),((7:ℚ)/50),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-2011623390434717666657144838657684420397185213427692819281:ℚ)/25229491200000000000000000000000000000000000000000000000000),((-30201901:ℚ)/128000000)⟩
theorem valid14 : Valid source36 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC16
#check @N11Formalization.C450Source36GroupedC16.bound
#print axioms N11Formalization.C450Source36GroupedC16.valid0
#print axioms N11Formalization.C450Source36GroupedC16.valid1
#print axioms N11Formalization.C450Source36GroupedC16.valid2
#print axioms N11Formalization.C450Source36GroupedC16.valid3
#print axioms N11Formalization.C450Source36GroupedC16.valid4
#print axioms N11Formalization.C450Source36GroupedC16.valid5
#print axioms N11Formalization.C450Source36GroupedC16.valid6
#print axioms N11Formalization.C450Source36GroupedC16.valid7
#print axioms N11Formalization.C450Source36GroupedC16.valid8
#print axioms N11Formalization.C450Source36GroupedC16.valid9
#print axioms N11Formalization.C450Source36GroupedC16.valid10
#print axioms N11Formalization.C450Source36GroupedC16.valid11
#print axioms N11Formalization.C450Source36GroupedC16.valid12
#print axioms N11Formalization.C450Source36GroupedC16.valid13
#print axioms N11Formalization.C450Source36GroupedC16.valid14
#print axioms N11Formalization.C450Source36GroupedC16.bound
#print axioms N11Formalization.C450Source36GroupedC16.endpoint_checks
