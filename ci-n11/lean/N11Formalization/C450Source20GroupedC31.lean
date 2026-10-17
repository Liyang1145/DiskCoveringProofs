import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((1370464201:ℚ)/2500000000),((3017946333:ℚ)/5000000000),((11033249407:ℚ)/13350000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((956404151:ℚ)/1250000000),((-3288095033499261990555048373858461527:ℚ)/29740879687500000000000000000000000000),((-42910186611265552203608619:ℚ)/115520000000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((1489314677:ℚ)/2500000000),((3136852991:ℚ)/5000000000),((11865202739:ℚ)/13825000000),((10626558973:ℚ)/10680000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6699546451:ℚ)/10000000000),((-3131357889280978686943141276727860908054839012754853247:ℚ)/24772320849609375000000000000000000000000000000000000000),((-2224743384214037249233329:ℚ)/6080000000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((3097469461:ℚ)/5000000000),((1302299689:ℚ)/2000000000),((24562286227:ℚ)/28600000000),((4393299067:ℚ)/4424000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((6178538979:ℚ)/10000000000),((-9243331939812854087094184401365753373696829670006204317:ℚ)/73105175000000000000000000000000000000000000000000000000),((-166493479581322496375368899:ℚ)/462080000000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((402037947:ℚ)/625000000),((828798437:ℚ)/1250000000),((3174265629:ℚ)/3634375000),((253672301:ℚ)/260000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2808079347:ℚ)/5000000000),((-20047551773240863155625573125038508421689496630770499:ℚ)/150016569805145263671875000000000000000000000000000000),((-7744525098721063904682113:ℚ)/21660000000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((327571857:ℚ)/500000000),((674927207:ℚ)/1000000000),((860334333:ℚ)/985000000),((2267981621:ℚ)/2326000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((332207967:ℚ)/625000000),((-99681051789231095933859197510914834796441603017963:ℚ)/746618457031250000000000000000000000000000000000000),((-4917726008011315225944593:ℚ)/13862400000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((3335132277:ℚ)/5000000000),((6868152379:ℚ)/10000000000),((26225925939:ℚ)/30025000000),((23036457137:ℚ)/23640000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2499125619:ℚ)/5000000000),((-2820858439783799584189889065923240214908783023088656061:ℚ)/21146528332519531250000000000000000000000000000000000000),((-487896632098048832896252553:ℚ)/1386240000000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((6789089517:ℚ)/10000000000),((6987028623:ℚ)/10000000000),((53283626619:ℚ)/61000000000),((23393085869:ℚ)/24020000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((932317961:ℚ)/2000000000),((-94546411413421392743338296684422746136239829707930549101:ℚ)/709315625000000000000000000000000000000000000000000000000),((-1936086774395629203987420473:ℚ)/5544960000000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((3453956071:ℚ)/5000000000),((1776475247:ℚ)/2500000000),((27057692497:ℚ)/30975000000),((5937425741:ℚ)/6100000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((4300718191:ℚ)/10000000000),((-12370472986172947677311492555448978716396839044287376823:ℚ)/92871822216796875000000000000000000000000000000000000000),((-160049259718457795305452779:ℚ)/462080000000000000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((3513366269:ℚ)/5000000000),((1806192413:ℚ)/2500000000),((27473563883:ℚ)/31450000000),((6026577239:ℚ)/6195000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1954453349:ℚ)/5000000000),((-9705200122551762667170596423536120413421635975502826471:ℚ)/72907672558593750000000000000000000000000000000000000000),((-158758294294977001594575859:ℚ)/462080000000000000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((1277:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((1429110161:ℚ)/2000000000),((367181739:ℚ)/500000000),((11155771127:ℚ)/12770000000),((1223145217:ℚ)/1258000000),((2337671911:ℚ)/2500000000),((9372267491:ℚ)/10000000000),((181171659:ℚ)/500000000),((3475674371:ℚ)/10000000000),((-54112013300364789302528859710115312713271155112981577:ℚ)/406726744726562500000000000000000000000000000000000000),((-25194826631124235659461499:ℚ)/73932800000000000000000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((629:ℚ)/800) ((1277:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1277:ℚ)/1600),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((22701147:ℚ)/31250000),((7462496527:ℚ)/10000000000),((58969343:ℚ)/67500000),((24819489581:ℚ)/25540000000),((9331481479:ℚ)/10000000000),((9350687649:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2982990623:ℚ)/10000000000),((-42601046636765990149746092326127464300821852731:ℚ)/320361328125000000000000000000000000000000000000),((-292832577111994456064033:ℚ)/866400000000000000000000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell ((1277:ℚ)/1600) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),((343:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((7383181331:ℚ)/10000000000),((317516501:ℚ)/400000000),((57442269317:ℚ)/68600000000),(1:ℚ),((57977633:ℚ)/62500000),((2332870371:ℚ)/2500000000),((1913736159:ℚ)/5000000000),((23943877:ℚ)/100000000),((-21840529890012934062835830299505963769710761499824319761:ℚ)/189157532812500000000000000000000000000000000000000000000),((-618728698233943502214448659:ℚ)/1848320000000000000000000000)⟩
theorem valid11 : Valid source20 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((343:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((343:ℚ)/400),((181:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((3929210337:ℚ)/5000000000),((2103321201:ℚ)/2500000000),((30384472359:ℚ)/36200000000),(1:ℚ),((9252071821:ℚ)/10000000000),((1855284257:ℚ)/2000000000),((1946075537:ℚ)/5000000000),(0:ℚ),((-690108820633274999067526239448605990847736953861871369:ℚ)/5929741000000000000000000000000000000000000000000000000),((-2678611:ℚ)/8000000)⟩
theorem valid12 : Valid source20 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source20 nn0 nn1 Qcell ((343:ℚ)/400) ((181:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((8333634877:ℚ)/10000000000),((2340980789:ℚ)/2500000000),((64095444139:ℚ)/80000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-39709127593399476005026416149143930478337803808326792941:ℚ)/400000000000000000000000000000000000000000000000000000000),((-2678611:ℚ)/8000000)⟩
theorem valid13 : Valid source20 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source20 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((4642001099:ℚ)/5000000000),((6582798563:ℚ)/5000000000),((35374007693:ℚ)/55200000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-690660563839338435409872383050594369:ℚ)/21024576000000000000000000000000000000),((-2678611:ℚ)/8000000)⟩
theorem valid14 : Valid source20 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((61:ℚ)/80) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source20 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source20 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC31
#check @N11Formalization.C450Source20GroupedC31.bound
#print axioms N11Formalization.C450Source20GroupedC31.valid0
#print axioms N11Formalization.C450Source20GroupedC31.valid1
#print axioms N11Formalization.C450Source20GroupedC31.valid2
#print axioms N11Formalization.C450Source20GroupedC31.valid3
#print axioms N11Formalization.C450Source20GroupedC31.valid4
#print axioms N11Formalization.C450Source20GroupedC31.valid5
#print axioms N11Formalization.C450Source20GroupedC31.valid6
#print axioms N11Formalization.C450Source20GroupedC31.valid7
#print axioms N11Formalization.C450Source20GroupedC31.valid8
#print axioms N11Formalization.C450Source20GroupedC31.valid9
#print axioms N11Formalization.C450Source20GroupedC31.valid10
#print axioms N11Formalization.C450Source20GroupedC31.valid11
#print axioms N11Formalization.C450Source20GroupedC31.valid12
#print axioms N11Formalization.C450Source20GroupedC31.valid13
#print axioms N11Formalization.C450Source20GroupedC31.valid14
#print axioms N11Formalization.C450Source20GroupedC31.bound
#print axioms N11Formalization.C450Source20GroupedC31.endpoint_checks
