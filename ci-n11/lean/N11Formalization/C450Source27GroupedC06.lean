import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((6775660531:ℚ)/10000000000),((174711353:ℚ)/250000000),((-1521824883:ℚ)/2480000000),((-5111660531:ℚ)/10110000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((235037543:ℚ)/500000000),((24394761336926090381350458980346837987723635405968715595781:ℚ)/97440021475200000000000000000000000000000000000000000000000),((6246735814473301584062697707:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((6895345009:ℚ)/10000000000),((1762063447:ℚ)/2500000000),((-15382697917:ℚ)/25275000000),((-5231345009:ℚ)/10205000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((4340208347:ℚ)/10000000000),((7180369851268612800774877689396451705391277269568565763659:ℚ)/29192885740318542480468750000000000000000000000000000000000),((6214456091842315716974736147:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((217349189:ℚ)/312500000),((355402277:ℚ)/500000000),((-3109425047:ℚ)/5102500000),((-165349189:ℚ)/321875000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((4149053461:ℚ)/10000000000),((2170000065669292174238139388316063348776457437807264801449:ℚ)/8808531402039941406250000000000000000000000000000000000000),((16766961108460735634307:ℚ)/40000000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((3507497309:ℚ)/5000000000),((7137938517:ℚ)/10000000000),((-62517323687:ℚ)/103000000000),((-2675497309:ℚ)/5173750000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((987311297:ℚ)/2500000000),((285755856321241508281515829957539881286351623719802363031552281:ℚ)/1169991062647937500000000000000000000000000000000000000000000000),((1545427874047169717277007947:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((35224509:ℚ)/50000000),((1791957399:ℚ)/2500000000),((-15711531389:ℚ)/25868750000),((-26904509:ℚ)/51975000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((3845675327:ℚ)/10000000000),((371132581150474726725687139967135242983570042920827794658639:ℚ)/1518324537722521591186523437500000000000000000000000000000000),((463008952227721815649441:ℚ)/1108992000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7074806953:ℚ)/10000000000),((1439543761:ℚ)/2000000000),((-467962273:ℚ)/770000000),((-5410806953:ℚ)/10442500000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((3739391687:ℚ)/10000000000),((276782381480031656519006928654963732578153158773587460221:ℚ)/1131432024198437500000000000000000000000000000000000000000),((6165164832192324995835106083:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((888088763:ℚ)/1250000000),((903450771:ℚ)/1250000000),((-7937958481:ℚ)/13053125000),((-680088763:ℚ)/1311250000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3630155293:ℚ)/10000000000),((936189394745348683008111180044998639640493554823692038542743:ℚ)/3823970147661515855789184570312500000000000000000000000000000),((96200748471306760109020603:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-11:ℚ)/16),((-5:ℚ)/8),((7134611281:ℚ)/10000000000),((7257491711:ℚ)/10000000000),((-63832408821:ℚ)/104900000000),((-5470611281:ℚ)/10537500000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((703538087:ℚ)/2000000000),((12561571206603280655277179583842306794304775775944303890403043:ℚ)/51269800930700062500000000000000000000000000000000000000000000),((6148501904403405847927130707:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7164510511:ℚ)/10000000000),((7287375459:ℚ)/10000000000),((-64161130049:ℚ)/105375000000),((-5500510511:ℚ)/10585000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((1700838127:ℚ)/5000000000),((297632359728044611110291498959008327514549120020723206963910101:ℚ)/1213865958023059082031250000000000000000000000000000000000000000),((6140126837200786366093260627:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((359720391:ℚ)/500000000),((1829314359:ℚ)/2500000000),((-16122457949:ℚ)/26462500000),((-276520391:ℚ)/531625000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((640964:ℚ)/1953125),((514036520750542696644615215015202769184317131741274450446673227:ℚ)/2094900477997613732910156250000000000000000000000000000000000000),((45987920242643766490959241:ℚ)/110899200000000000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((1444860647:ℚ)/2000000000),((7347137667:ℚ)/10000000000),((-64818514337:ℚ)/106325000000),((-1112060647:ℚ)/2136000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((315742059:ℚ)/1000000000),((32877187244380652275389915451201460581041160730932555164982039:ℚ)/133890179224244458007812500000000000000000000000000000000000000),((244931579517439934242898883:ℚ)/591462400000000000000000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-11:ℚ)/16),((-5:ℚ)/8),((7254196781:ℚ)/10000000000),((7406892981:ℚ)/10000000000),((-65475822791:ℚ)/106800000000),((-5590196781:ℚ)/10775000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3028191559:ℚ)/10000000000),((456895631999896120463995979298731461134318869078472106243459:ℚ)/1841565183876562500000000000000000000000000000000000000000000),((6114827202488562969180417707:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((7142557:ℚ)/9765625),((1493328317:ℚ)/2000000000),((-13226611487:ℚ)/21550000000),((-44140456:ℚ)/84921875),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((344024353:ℚ)/1250000000),((18359453323419216736511308471908854791456994259864162954872969:ℚ)/73906209541311718750000000000000000000000000000000000000000000),((23261319738701251809377:ℚ)/56406250000000000000000)⟩
theorem valid12 : Valid source27 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source27 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((921719097:ℚ)/1250000000),((3793059681:ℚ)/5000000000),((-33723656491:ℚ)/54350000000),((-101959871:ℚ)/197500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2446150367:ℚ)/10000000000),((24788747478437420265094555507773585026699177405219249887053:ℚ)/97848206838659667968750000000000000000000000000000000000000),((285032216439222808104941449:ℚ)/693120000000000000000000000)⟩
theorem valid13 : Valid source27 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((1498656161:ℚ)/2000000000),((7825001761:ℚ)/10000000000),((-10010717053:ℚ)/15800000000),((-1165856161:ℚ)/2288000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1677795337:ℚ)/10000000000),((10190154548347050350476552258071810625876037917597151439607:ℚ)/38777517350000000000000000000000000000000000000000000000000),((241843282038983167202322227:ℚ)/591462400000000000000000000)⟩
theorem valid14 : Valid source27 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((7732258611:ℚ)/10000000000),((1755942963:ℚ)/2000000000),((-16115372593:ℚ)/22880000000),((-6068258611:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((3953228004627405207554974019548079528453071517348270217361:ℚ)/12593704780800000000000000000000000000000000000000000000000),((416536377:ℚ)/1024000000)⟩
theorem valid15 : Valid source27 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((8687296507:ℚ)/10000000000),((1068644047:ℚ)/1000000000),((-10155084517:ℚ)/12960000000),((-7023296507:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1665680645035410660980222841547496197486598525964070577:ℚ)/4534963200000000000000000000000000000000000000000000000),((416536377:ℚ)/1024000000)⟩
theorem valid16 : Valid source27 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((662155293:ℚ)/625000000),((2898863749:ℚ)/2000000000),((-28687501239:ℚ)/32000000000),((-558155293:ℚ)/1380000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((18033779184714013365727199320646720179819:ℚ)/39002112000000000000000000000000000000000),((416536377:ℚ)/1024000000)⟩
theorem valid17 : Valid source27 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source27 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4139:ℚ)/6400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((4139:ℚ)/6400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source27 nn0 nn1 Qcell ((4139:ℚ)/6400) ((4177:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source27 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source27 nn0 nn1 Qcell ((4177:ℚ)/6400) ((2117:ℚ)/3200) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source27 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2117:ℚ)/3200) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source27 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source27 nn0 nn1 Qcell ((2117:ℚ)/3200) ((1087:ℚ)/1600) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source27 nn0 nn1 Qcell ((2117:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC06
#check @N11Formalization.C450Source27GroupedC06.bound
#print axioms N11Formalization.C450Source27GroupedC06.valid0
#print axioms N11Formalization.C450Source27GroupedC06.valid1
#print axioms N11Formalization.C450Source27GroupedC06.valid2
#print axioms N11Formalization.C450Source27GroupedC06.valid3
#print axioms N11Formalization.C450Source27GroupedC06.valid4
#print axioms N11Formalization.C450Source27GroupedC06.valid5
#print axioms N11Formalization.C450Source27GroupedC06.valid6
#print axioms N11Formalization.C450Source27GroupedC06.valid7
#print axioms N11Formalization.C450Source27GroupedC06.valid8
#print axioms N11Formalization.C450Source27GroupedC06.valid9
#print axioms N11Formalization.C450Source27GroupedC06.valid10
#print axioms N11Formalization.C450Source27GroupedC06.valid11
#print axioms N11Formalization.C450Source27GroupedC06.valid12
#print axioms N11Formalization.C450Source27GroupedC06.valid13
#print axioms N11Formalization.C450Source27GroupedC06.valid14
#print axioms N11Formalization.C450Source27GroupedC06.valid15
#print axioms N11Formalization.C450Source27GroupedC06.valid16
#print axioms N11Formalization.C450Source27GroupedC06.valid17
#print axioms N11Formalization.C450Source27GroupedC06.bound
#print axioms N11Formalization.C450Source27GroupedC06.endpoint_checks
