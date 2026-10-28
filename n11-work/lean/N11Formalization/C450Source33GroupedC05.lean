import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((3493380427:ℚ)/5000000000),((7221773039:ℚ)/10000000000),((-16705319117:ℚ)/24800000000),((-28187184697:ℚ)/50550000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2022355837:ℚ)/5000000000),((313542968911991047970099735215902643173980381:ℚ)/794450497672800000000000000000000000000000000),((33992808449475916612928321:ℚ)/57760000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7106759171:ℚ)/10000000000),((1456336641:ℚ)/2000000000),((-3377009923:ℚ)/5055000000),((-57694350881:ℚ)/102050000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((724510991:ℚ)/2000000000),((5516287861111110477132347113977994921457633972812674922440379:ℚ)/14144256331392319335937500000000000000000000000000000000000000),((135401074657483840764726609:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((716674063:ℚ)/1000000000),((917697921:ℚ)/1250000000),((-2133093763:ℚ)/3189062500),((-5835414693:ℚ)/10300000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((424108803:ℚ)/1250000000),((262386634569396531291410669083670193948744189771984106349:ℚ)/673365695575000000000000000000000000000000000000000000000),((1351483497323975215656681:ℚ)/2310400000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7226710733:ℚ)/10000000000),((3700736903:ℚ)/5000000000),((-8622210709:ℚ)/12875000000),((-59013818063:ℚ)/103950000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((3147203203:ℚ)/10000000000),((1618173633140969281747685879659329170892695636518284143777:ℚ)/4156137837644348144531250000000000000000000000000000000000),((134892939997330083963189361:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((3643334899:ℚ)/5000000000),((7461354789:ℚ)/10000000000),((-17424064367:ℚ)/25987500000),((-29836683889:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((2881461477:ℚ)/10000000000),((7221138329438067432048320390744684440428024361063273562023253:ℚ)/18561205492017890625000000000000000000000000000000000000000000),((33658711392939209501249649:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((734661813:ℚ)/1000000000),((3790544707:ℚ)/5000000000),((-8891634121:ℚ)/13112500000),((-6033279943:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((1294732421:ℚ)/5000000000),((36537482814408134821677533141815628261587637243339556921199:ℚ)/93089831108280000000000000000000000000000000000000000000000),((1344467608338755184287681:ℚ)/2310400000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((7466483763:ℚ)/10000000000),((3910227991:ℚ)/5000000000),((-9250683973:ℚ)/13350000000),((-61651321393:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1877211069:ℚ)/10000000000),((1145827286886623589816318157836334463765343149430860202813341:ℚ)/2870441010465000000000000000000000000000000000000000000000000),((133794735637058542197114481:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((1541219701:ℚ)/2000000000),((8059697179:ℚ)/10000000000),((-19219091537:ℚ)/27650000000),((-12857416711:ℚ)/22880000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((911109847994245656130823006872096953371088519373340077495207:ℚ)/2289276975265280000000000000000000000000000000000000000000000),((1842521:ℚ)/3200000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((7945571:ℚ)/10000000),((9015631573:ℚ)/10000000000),((-22086894719:ℚ)/28600000000),((-66921281:ℚ)/129600000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((9104925228127487744778180330687575618887645217867099:ℚ)/20865479057280000000000000000000000000000000000000000),((1842521:ℚ)/3200000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((2225573077:ℚ)/2500000000),((5462047773:ℚ)/5000000000),((-13906143319:ℚ)/16200000000),((-19361303847:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1443204591156270754414566853386761:ℚ)/3037500000000000000000000000000000),((1842521:ℚ)/3200000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((2702968823:ℚ)/2500000000),((1841750563:ℚ)/1250000000),((-4905251689:ℚ)/5000000000),((-24612657053:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1722459387859123593308977:ℚ)/3125000000000000000000000),((1842521:ℚ)/3200000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source33 nn0 nn1 Qcell ((2041:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source33 nn0 nn1 Qcell ((1049:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source33 nn0 nn1 Qcell ((1049:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC05
#check @N11Formalization.C450Source33GroupedC05.bound
#print axioms N11Formalization.C450Source33GroupedC05.valid0
#print axioms N11Formalization.C450Source33GroupedC05.valid1
#print axioms N11Formalization.C450Source33GroupedC05.valid2
#print axioms N11Formalization.C450Source33GroupedC05.valid3
#print axioms N11Formalization.C450Source33GroupedC05.valid4
#print axioms N11Formalization.C450Source33GroupedC05.valid5
#print axioms N11Formalization.C450Source33GroupedC05.valid6
#print axioms N11Formalization.C450Source33GroupedC05.valid7
#print axioms N11Formalization.C450Source33GroupedC05.valid8
#print axioms N11Formalization.C450Source33GroupedC05.valid9
#print axioms N11Formalization.C450Source33GroupedC05.valid10
#print axioms N11Formalization.C450Source33GroupedC05.bound
#print axioms N11Formalization.C450Source33GroupedC05.endpoint_checks
