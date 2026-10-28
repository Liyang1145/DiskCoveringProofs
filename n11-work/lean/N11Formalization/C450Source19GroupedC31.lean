import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((5519935429:ℚ)/10000000000),((6071877083:ℚ)/10000000000),((44079548003:ℚ)/53400000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7578619621:ℚ)/10000000000),((-40270283728030956796356484102325569351:ℚ)/380683260000000000000000000000000000000),((-322824977721258431534582219:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((5995296093:ℚ)/10000000000),((6309656493:ℚ)/10000000000),((47407072651:ℚ)/55300000000),((7077656493:ℚ)/7120000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6618530349:ℚ)/10000000000),((-383725000377806436149570177171164089975628802459704289971:ℚ)/3170857068750000000000000000000000000000000000000000000000),((-954445257068068253403507473:ℚ)/2772480000000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((3116478909:ℚ)/5000000000),((654741731:ℚ)/1000000000),((24535352363:ℚ)/28600000000),((2194625193:ℚ)/2212000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1522912709:ℚ)/2500000000),((-17701443212817767786956328841838181616935970075931268601:ℚ)/146210350000000000000000000000000000000000000000000000000),((-235074917362569230148717137:ℚ)/693120000000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((6470608789:ℚ)/10000000000),((3333145659:ℚ)/5000000000),((50734261523:ℚ)/58150000000),((11151436977:ℚ)/11440000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2760777471:ℚ)/5000000000),((-157287592128648841635433039992956580350830515740777193249:ℚ)/1228935739843750000000000000000000000000000000000000000000),((-311099543328513112462762539:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((6589430571:ℚ)/10000000000),((1696290333:ℚ)/2500000000),((51566013997:ℚ)/59100000000),((5664870999:ℚ)/5815000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5215853949:ℚ)/10000000000),((-4582747410947684169393558874660276501635853273662197951:ℚ)/35837685937500000000000000000000000000000000000000000000),((-926230959895344492927590657:ℚ)/2772480000000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((1677062511:ℚ)/2500000000),((863003443:ℚ)/1250000000),((13099437577:ℚ)/15012500000),((959003443:ℚ)/985000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2446474481:ℚ)/5000000000),((-2026479305147481854921233147098792145777248092423518177:ℚ)/15859896249389648437500000000000000000000000000000000000),((-57447800229983405118139817:ℚ)/173280000000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((6827067317:ℚ)/10000000000),((6963459279:ℚ)/10000000000),((5914385691:ℚ)/6725000000),((23194377837:ℚ)/24020000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((568643887:ℚ)/1250000000),((-62273742695756816086516025376974184687455559374832033:ℚ)/475222387695312500000000000000000000000000000000000000),((-305223033271971114312931051:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((172161879:ℚ)/250000000),((702289013:ℚ)/1000000000),((1341133153:ℚ)/1525000000),((779089013:ℚ)/807000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((174715161:ℚ)/400000000),((-8708910039219224506357493395709130113245780749801553:ℚ)/66498339843750000000000000000000000000000000000000000),((-570085801236652105959857:ℚ)/1732800000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((1736470623:ℚ)/2500000000),((7141749259:ℚ)/10000000000),((13515294361:ℚ)/15487500000),((23729247777:ℚ)/24400000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((261204927:ℚ)/625000000),((-2962629201965922611846391120382401858976870458196860427:ℚ)/23217955554199218750000000000000000000000000000000000000),((-56564811936715927710745433:ℚ)/173280000000000000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((7064695667:ℚ)/10000000000),((7260605087:ℚ)/10000000000),((54892869669:ℚ)/62900000000),((8028605087:ℚ)/8260000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((377564603:ℚ)/1000000000),((-49588181042584516328304572690434136820500706184421219583:ℚ)/388840920312500000000000000000000000000000000000000000000),((-299325104993961541519238651:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((629:ℚ)/800),((1277:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((7183506933:ℚ)/10000000000),((3689728881:ℚ)/5000000000),((55724548531:ℚ)/63850000000),((12221186643:ℚ)/12580000000),((2337671911:ℚ)/2500000000),((9372267491:ℚ)/10000000000),((181171659:ℚ)/500000000),((3325949599:ℚ)/10000000000),((-12960792951540040195492123865288521940099111590751572393:ℚ)/101681686181640625000000000000000000000000000000000000000),((-890915113852521627473369153:ℚ)/2772480000000000000000000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((1277:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1277:ℚ)/1600),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((7302316373:ℚ)/10000000000),((7498307423:ℚ)/10000000000),((18852071537:ℚ)/21600000000),((24798922269:ℚ)/25540000000),((9331481479:ℚ)/10000000000),((9350687649:ℚ)/10000000000),((735446993:ℚ)/2000000000),((561621251:ℚ)/2000000000),((-2674976642515390576032109670925485261411494226844344633:ℚ)/20995200000000000000000000000000000000000000000000000000),((-294618793081781241925584811:ℚ)/924160000000000000000000000)⟩
theorem valid11 : Valid source19 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source19 nn0 nn1 Qcell ((1277:ℚ)/1600) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),((343:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((742112407:ℚ)/1000000000),((797367843:ℚ)/1000000000),((5738786849:ℚ)/6860000000),(1:ℚ),((57977633:ℚ)/62500000),((2332870371:ℚ)/2500000000),((1913736159:ℚ)/5000000000),((434780099:ℚ)/2000000000),((-41848470562219794777100092137637172909791532389308201:ℚ)/378315065625000000000000000000000000000000000000000000),((-2926097498531285892573491:ℚ)/9241600000000000000000000)⟩
theorem valid12 : Valid source19 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((343:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((343:ℚ)/400),((181:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((3948169433:ℚ)/5000000000),((8449010451:ℚ)/10000000000),((30357186031:ℚ)/36200000000),(1:ℚ),((9252071821:ℚ)/10000000000),((1855284257:ℚ)/2000000000),((1946075537:ℚ)/5000000000),(0:ℚ),((-1322563452672700552515940942420663889713393672395866117:ℚ)/11859482000000000000000000000000000000000000000000000000),((-1013333:ℚ)/3200000)⟩
theorem valid13 : Valid source19 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source19 nn0 nn1 Qcell ((343:ℚ)/400) ((181:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((8371531101:ℚ)/10000000000),((1174947473:ℚ)/1250000000),((64040717707:ℚ)/80000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-76100905011596791837157756601453494666841577611670987409:ℚ)/800000000000000000000000000000000000000000000000000000000),((-1013333:ℚ)/3200000)⟩
theorem valid14 : Valid source19 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source19 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((1864372151:ℚ)/2000000000),((13201072813:ℚ)/10000000000),((614721959:ℚ)/960000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-6946268674778606709114230587831:ℚ)/221184000000000000000000000000000),((-1013333:ℚ)/3200000)⟩
theorem valid15 : Valid source19 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((61:ℚ)/80) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source19 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC31
#check @N11Formalization.C450Source19GroupedC31.bound
#print axioms N11Formalization.C450Source19GroupedC31.valid0
#print axioms N11Formalization.C450Source19GroupedC31.valid1
#print axioms N11Formalization.C450Source19GroupedC31.valid2
#print axioms N11Formalization.C450Source19GroupedC31.valid3
#print axioms N11Formalization.C450Source19GroupedC31.valid4
#print axioms N11Formalization.C450Source19GroupedC31.valid5
#print axioms N11Formalization.C450Source19GroupedC31.valid6
#print axioms N11Formalization.C450Source19GroupedC31.valid7
#print axioms N11Formalization.C450Source19GroupedC31.valid8
#print axioms N11Formalization.C450Source19GroupedC31.valid9
#print axioms N11Formalization.C450Source19GroupedC31.valid10
#print axioms N11Formalization.C450Source19GroupedC31.valid11
#print axioms N11Formalization.C450Source19GroupedC31.valid12
#print axioms N11Formalization.C450Source19GroupedC31.valid13
#print axioms N11Formalization.C450Source19GroupedC31.valid14
#print axioms N11Formalization.C450Source19GroupedC31.valid15
#print axioms N11Formalization.C450Source19GroupedC31.bound
#print axioms N11Formalization.C450Source19GroupedC31.endpoint_checks
