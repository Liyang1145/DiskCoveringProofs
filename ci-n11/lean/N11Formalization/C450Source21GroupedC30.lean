import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((5487891399:ℚ)/10000000000),((151069503:ℚ)/250000000),((83502588187:ℚ)/106800000000),((1217486521:ℚ)/1240000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1527952473:ℚ)/2000000000),((-26223290922948301112631565099959912511:ℚ)/211490700000000000000000000000000000000),((-10066278026954713316562251:ℚ)/27724800000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((596375457:ℚ)/1000000000),((392549183:ℚ)/625000000),((8968880941:ℚ)/11060000000),((1049281427:ℚ)/1112500000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6685769783:ℚ)/10000000000),((-1209751321071590653844929058832924350407150128421001781:ℚ)/8455618850000000000000000000000000000000000000000000000),((-20672678959370973806629657:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((6201641559:ℚ)/10000000000),((1303751993:ℚ)/2000000000),((8434667297:ℚ)/10400000000),((10406263951:ℚ)/11060000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((61632983:ℚ)/100000000),((-1006592090059339491566984218803290985475199764908193257:ℚ)/7030400000000000000000000000000000000000000000000000000),((-208618869555721957489780937:ℚ)/591462400000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((6439502781:ℚ)/10000000000),((3318867429:ℚ)/5000000000),((95873536153:ℚ)/116300000000),((26432072003:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5599098437:ℚ)/10000000000),((-373051882692228697152943804302234389973592521905048377177:ℚ)/2457871479687500000000000000000000000000000000000000000000),((-3882755661406501061860487699:ℚ)/11089920000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6558424521:ℚ)/10000000000),((3378351251:ℚ)/5000000000),((97419518773:ℚ)/118200000000),((26848458757:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2648580123:ℚ)/5000000000),((-391267265628072316889941450835762714490295353003362280173:ℚ)/2580313387500000000000000000000000000000000000000000000000),((-1284619611137036404332235713:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((834667591:ℚ)/1250000000),((6875663241:ℚ)/10000000000),((12370678683:ℚ)/15012500000),((54529642687:ℚ)/59100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2489394839:ℚ)/5000000000),((-3203689708782322880646444550935138922665555875886930267:ℚ)/21146528332519531250000000000000000000000000000000000000),((-15299652982515984910119379259:ℚ)/44359680000000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((1359250333:ℚ)/2000000000),((3497308699:ℚ)/5000000000),((20102254329:ℚ)/24400000000),((27681160893:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1160144683:ℚ)/2500000000),((-13743252074219224318613712002178006726039507096690471969:ℚ)/90792400000000000000000000000000000000000000000000000000),((-1265306276014908523383054513:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((345757879:ℚ)/500000000),((7113565279:ℚ)/10000000000),((1700950809:ℚ)/2065000000),((56194956953:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((4277795349:ℚ)/10000000000),((-2080972213803430988875992038833758553243279192340489:ℚ)/13758788476562500000000000000000000000000000000000000),((-5022500685665482697467900633:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((7034058703:ℚ)/10000000000),((226015849:ℚ)/312500000),((103602763139:ℚ)/125800000000),((594036981:ℚ)/645312500),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((3883528301:ℚ)/10000000000),((-1836414445723762398575387050739982866648386710715327691:ℚ)/12151278759765625000000000000000000000000000000000000000),((-13481732033051089527233:ℚ)/40000000000000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((7152955253:ℚ)/10000000000),((1867593507:ℚ)/2500000000),((35049472763:ℚ)/43200000000),((14673154549:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((861739247:ℚ)/2500000000),((-2677839196507138626701551388173549527515233824515361409:ℚ)/18662400000000000000000000000000000000000000000000000000),((-919862899229330316508435811:ℚ)/2772480000000000000000000000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((92384193:ℚ)/125000000),((4210824269:ℚ)/5000000000),((1352994509:ℚ)/1810000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((2352110017:ℚ)/10000000000),((-246907281387608085745886504293381748009647179150461:ℚ)/2316305078125000000000000000000000000000000000000000),((-336803211:ℚ)/1024000000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((8341708907:ℚ)/10000000000),((4686340247:ℚ)/5000000000),((120602215791:ℚ)/160000000000),((36004381729:ℚ)/36200000000),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-705981744068913445529296845830769437260760646867694232079:ℚ)/6400000000000000000000000000000000000000000000000000000000),((-336803211:ℚ)/1024000000)⟩
theorem valid11 : Valid source21 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source21 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((9292497183:ℚ)/10000000000),((3293846519:ℚ)/2500000000),((132962463379:ℚ)/220800000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-25657527853172755970273859470502652811:ℚ)/897048576000000000000000000000000000000),((-336803211:ℚ)/1024000000)⟩
theorem valid12 : Valid source21 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((181:ℚ)/200) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source21 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC30
#check @N11Formalization.C450Source21GroupedC30.bound
#print axioms N11Formalization.C450Source21GroupedC30.valid0
#print axioms N11Formalization.C450Source21GroupedC30.valid1
#print axioms N11Formalization.C450Source21GroupedC30.valid2
#print axioms N11Formalization.C450Source21GroupedC30.valid3
#print axioms N11Formalization.C450Source21GroupedC30.valid4
#print axioms N11Formalization.C450Source21GroupedC30.valid5
#print axioms N11Formalization.C450Source21GroupedC30.valid6
#print axioms N11Formalization.C450Source21GroupedC30.valid7
#print axioms N11Formalization.C450Source21GroupedC30.valid8
#print axioms N11Formalization.C450Source21GroupedC30.valid9
#print axioms N11Formalization.C450Source21GroupedC30.valid10
#print axioms N11Formalization.C450Source21GroupedC30.valid11
#print axioms N11Formalization.C450Source21GroupedC30.valid12
#print axioms N11Formalization.C450Source21GroupedC30.bound
#print axioms N11Formalization.C450Source21GroupedC30.endpoint_checks
