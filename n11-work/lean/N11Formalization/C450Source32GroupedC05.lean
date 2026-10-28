import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((435215913:ℚ)/625000000),((899411677:ℚ)/1250000000),((-67685001:ℚ)/100000000),((-3547375043:ℚ)/6318750000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4121941:ℚ)/10000000),((4756718359052725746591082380750293:ℚ)/12614310681152343750000000000000000),((261207092587903006334171:ℚ)/451250000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((1416674503:ℚ)/2000000000),((7255170239:ℚ)/10000000000),((-5655170239:ℚ)/8425000000),((-11615419533:ℚ)/20410000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((1854207733:ℚ)/5000000000),((83451081182690987481581364926439530306645030559853835193:ℚ)/223845797529453125000000000000000000000000000000000000000),((2663728446325693090653131:ℚ)/4620800000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((1785828731:ℚ)/2500000000),((914379711:ℚ)/1250000000),((-2143139133:ℚ)/3189062500),((-14684116041:ℚ)/25750000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((3484301351:ℚ)/10000000000),((649057380815940033501719397359055224288914026024656367093:ℚ)/1742387349218750000000000000000000000000000000000000000000),((4154482023725961280149699:ℚ)/7220000000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((11255073:ℚ)/15625000),((7374896027:ℚ)/10000000000),((-17324688081:ℚ)/25750000000),((-92805803:ℚ)/162421875),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((3245459183:ℚ)/10000000000),((65481329699179019461320967050827853823479721513:ℚ)/175915757501497864723205566406250000000000000000),((5183508050697662819977:ℚ)/9025000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((7263168197:ℚ)/10000000000),((3717372753:ℚ)/5000000000),((-2917372753:ℚ)/4331250000),((-60054850167:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((2988353259:ℚ)/10000000000),((123980653490366977181841775037976681185889233765896049169781:ℚ)/333310087398750000000000000000000000000000000000000000000000),((66224783235144461583467331:ℚ)/115520000000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((3661539821:ℚ)/5000000000),((1510883769:ℚ)/2000000000),((-3572651307:ℚ)/5245000000),((-30356938031:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((2707779137:ℚ)/10000000000),((2774496162805688545719341194244331187594621540485448840961:ℚ)/7395124810000000000000000000000000000000000000000000000000),((16534014693116975149200819:ℚ)/28880000000000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((7442873523:ℚ)/10000000000),((3896834651:ℚ)/5000000000),((-3096834651:ℚ)/4450000000),((-62031608753:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1018483463:ℚ)/5000000000),((24601601051338746286245818589611379436229869149914111684369:ℚ)/64504292370000000000000000000000000000000000000000000000000),((65835823644158588599677811:ℚ)/115520000000000000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((7682352347:ℚ)/10000000000),((4016401133:ℚ)/5000000000),((-9649203399:ℚ)/13825000000),((-64665875817:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((393623524917859094594603002668400761852752127716892901917117:ℚ)/1034935341440000000000000000000000000000000000000000000000000),((4528897:ℚ)/8000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((7921698173:ℚ)/10000000000),((2247092081:ℚ)/2500000000),((-5541276243:ℚ)/7150000000),((-22432893301:ℚ)/43200000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((4494233184956599497494934650004289375354892378414356205293:ℚ)/10808328960000000000000000000000000000000000000000000000000),((4528897:ℚ)/8000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((8877988573:ℚ)/10000000000),((5448154123:ℚ)/5000000000),((-4648154123:ℚ)/5400000000),((-77817874303:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((130015373942765054181508370912952531533:ℚ)/288000000000000000000000000000000000000),((4528897:ℚ)/8000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((10786958891:ℚ)/10000000000),((3676401313:ℚ)/2500000000),((-9829203939:ℚ)/10000000000),((-32938849267:ℚ)/73600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1406569902882338640580530287:ℚ)/2708480000000000000000000000),((4528897:ℚ)/8000000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source32 nn0 nn1 Qcell ((2041:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source32 nn0 nn1 Qcell ((1049:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source32 nn0 nn1 Qcell ((1049:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC05
#check @N11Formalization.C450Source32GroupedC05.bound
#print axioms N11Formalization.C450Source32GroupedC05.valid0
#print axioms N11Formalization.C450Source32GroupedC05.valid1
#print axioms N11Formalization.C450Source32GroupedC05.valid2
#print axioms N11Formalization.C450Source32GroupedC05.valid3
#print axioms N11Formalization.C450Source32GroupedC05.valid4
#print axioms N11Formalization.C450Source32GroupedC05.valid5
#print axioms N11Formalization.C450Source32GroupedC05.valid6
#print axioms N11Formalization.C450Source32GroupedC05.valid7
#print axioms N11Formalization.C450Source32GroupedC05.valid8
#print axioms N11Formalization.C450Source32GroupedC05.valid9
#print axioms N11Formalization.C450Source32GroupedC05.valid10
#print axioms N11Formalization.C450Source32GroupedC05.bound
#print axioms N11Formalization.C450Source32GroupedC05.endpoint_checks
