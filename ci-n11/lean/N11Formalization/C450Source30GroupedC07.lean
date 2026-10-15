import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((27041827:ℚ)/40000000),((6978529131:ℚ)/10000000000),((-5186529131:ℚ)/9920000000),((-169136443:ℚ)/404400000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2372363169:ℚ)/5000000000),((8003681101536057511253:ℚ)/27256560000000000000000),((392188920711274624779:ℚ)/1182924800000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((68805281:ℚ)/100000000),((3519258763:ℚ)/5000000000),((-2623258763:ℚ)/5055000000),((-433647529:ℚ)/1020500000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((4386340179:ℚ)/10000000000),((382423602624108454393388583780252523:ℚ)/1316094840937500000000000000000000000),((2413575687547482682611:ℚ)/7393280000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((6940545023:ℚ)/10000000000),((7098494433:ℚ)/10000000000),((-5306494433:ℚ)/10205000000),((-43904905207:ℚ)/103000000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((4196548899:ℚ)/10000000000),((6290021605279696384501982091816629824361:ℚ)/21652969000000000000000000000000000000000),((23945877024028831990595379:ℚ)/73932800000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((1400109983:ℚ)/2000000000),((7158460173:ℚ)/10000000000),((-5366460173:ℚ)/10300000000),((-8888989847:ℚ)/20790000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((3998356339:ℚ)/10000000000),((1346795997523891010929247769277450789:ℚ)/4637404406250000000000000000000000000),((950190415499679099169139:ℚ)/2957312000000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((7060543113:ℚ)/10000000000),((451150941:ℚ)/625000000),((-339150941:ℚ)/649687500),((-44984888017:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((151617579:ℚ)/400000000),((33213061833695902015739993507121021064177:ℚ)/114386683950000000000000000000000000000000),((70687219945565369506314857:ℚ)/221798400000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7120524943:ℚ)/10000000000),((7278359381:ℚ)/10000000000),((-5486359381:ℚ)/10490000000),((-45524724487:ℚ)/105850000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((22319341:ℚ)/62500000),((233699782444799164893194734194602023723:ℚ)/805015712500000000000000000000000000000),((23368815496616173439526099:ℚ)/73932800000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((1436099143:ℚ)/2000000000),((7338293433:ℚ)/10000000000),((-5546293433:ℚ)/10585000000),((-9212892287:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((1669031817:ℚ)/5000000000),((77876911807994303978916091942266648989:ℚ)/268300112000000000000000000000000000000),((926959465823665018687299:ℚ)/2957312000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/8),((-9:ℚ)/16),((7240455731:ℚ)/10000000000),((739821749:ℚ)/1000000000),((-560621749:ℚ)/1068000000),((-46604101579:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3088243841:ℚ)/10000000000),((4498321986571458253637207594482324969909:ℚ)/15499433437500000000000000000000000000000),((22977919809049798117108011:ℚ)/73932800000000000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((7300405281:ℚ)/10000000000),((7458131819:ℚ)/10000000000),((-5666131819:ℚ)/10775000000),((-47143647529:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2817165579:ℚ)/10000000000),((7389250691452353142468767379258865804611:ℚ)/25462811950000000000000000000000000000000),((68341844143336848117327833:ℚ)/221798400000000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((1840086161:ℚ)/2500000000),((7577932313:ℚ)/10000000000),((-5785932313:ℚ)/10870000000),((-11920775449:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2517964869:ℚ)/10000000000),((304161340541444621038437558050387823427:ℚ)/1038794946875000000000000000000000000000),((1411379443815551385735571:ℚ)/4620800000000000000000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((3740096941:ℚ)/5000000000),((3908713651:ℚ)/5000000000),((-3012713651:ℚ)/5530000000),((-24380872469:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((35559027:ℚ)/200000000),((207295009251474216757880136695707066649:ℚ)/695895200000000000000000000000000000000),((5545316825177345036129131:ℚ)/18483200000000000000000000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((7538849:ℚ)/9765625),((54838907:ℚ)/62500000),((-3356839:ℚ)/5500000),((-49724641:ℚ)/126562500),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((256163799180494315417818064779367:ℚ)/783105468750000000000000000000000),((37700009:ℚ)/128000000)⟩
theorem valid11 : Valid source30 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((542305863:ℚ)/625000000),((10683916861:ℚ)/10000000000),((-2963972287:ℚ)/4320000000),((-3720752767:ℚ)/10000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1208575740147775232295449475608035033:ℚ)/3375000000000000000000000000000000000),((37700009:ℚ)/128000000)⟩
theorem valid12 : Valid source30 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((661689543:ℚ)/625000000),((2899051743:ℚ)/2000000000),((-2540651743:ℚ)/3200000000),((-4795205887:ℚ)/13800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((13183740221638423864959443:ℚ)/31740000000000000000000000),((37700009:ℚ)/128000000)⟩
theorem valid13 : Valid source30 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source30 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source30 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source30 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC07
#check @N11Formalization.C450Source30GroupedC07.bound
#print axioms N11Formalization.C450Source30GroupedC07.valid0
#print axioms N11Formalization.C450Source30GroupedC07.valid1
#print axioms N11Formalization.C450Source30GroupedC07.valid2
#print axioms N11Formalization.C450Source30GroupedC07.valid3
#print axioms N11Formalization.C450Source30GroupedC07.valid4
#print axioms N11Formalization.C450Source30GroupedC07.valid5
#print axioms N11Formalization.C450Source30GroupedC07.valid6
#print axioms N11Formalization.C450Source30GroupedC07.valid7
#print axioms N11Formalization.C450Source30GroupedC07.valid8
#print axioms N11Formalization.C450Source30GroupedC07.valid9
#print axioms N11Formalization.C450Source30GroupedC07.valid10
#print axioms N11Formalization.C450Source30GroupedC07.valid11
#print axioms N11Formalization.C450Source30GroupedC07.valid12
#print axioms N11Formalization.C450Source30GroupedC07.valid13
#print axioms N11Formalization.C450Source30GroupedC07.bound
#print axioms N11Formalization.C450Source30GroupedC07.endpoint_checks
