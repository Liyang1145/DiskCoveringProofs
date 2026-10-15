import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((1752481647:ℚ)/2500000000),((1812034707:ℚ)/2500000000),((-4156104121:ℚ)/6200000000),((-4665766039:ℚ)/8425000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((1983270879:ℚ)/5000000000),((151492312760945677816282347971977543664453:ℚ)/367801156330000000000000000000000000000000),((8627996547443973473353311:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((3565004061:ℚ)/5000000000),((1461616691:ℚ)/2000000000),((-3360850073:ℚ)/5055000000),((-28655044671:ℚ)/51025000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((883806731:ℚ)/2500000000),((2397221198672293472807705758573357377825635892881751822083167:ℚ)/5893440138080133056640625000000000000000000000000000000000000),((34364726289540914445032759:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((7190029991:ℚ)/10000000000),((3684008713:ℚ)/5000000000),((-8492026139:ℚ)/12756250000),((-57970329901:ℚ)/103000000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((12888909:ℚ)/39062500),((106719142356294119141457555536068107407522086689644718416324747:ℚ)/262612621274250000000000000000000000000000000000000000000000000),((137196103381470840613821199:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((3625019867:ℚ)/5000000000),((467990911:ℚ)/625000000),((-1083972733:ℚ)/1609375000),((-29315218537:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1523240003:ℚ)/5000000000),((15328377536685370421475032445847149252915888382426992803929:ℚ)/37372399185916137695312500000000000000000000000000000000000),((34250545807866861490558631:ℚ)/57760000000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((7370024193:ℚ)/10000000000),((1901913133:ℚ)/2500000000),((-4425739399:ℚ)/6556250000),((-19983422041:ℚ)/35600000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((616581597:ℚ)/2500000000),((127040970997794709497542301780880251976199405501769344943026897:ℚ)/310299437027600000000000000000000000000000000000000000000000000),((136453669632448083772687871:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((7489964067:ℚ)/10000000000),((3923569537:ℚ)/5000000000),((-9210708611:ℚ)/13350000000),((-61269604737:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1703730331:ℚ)/10000000000),((83722759980775885936257630153114623020399467065339863409363747:ℚ)/200930870732550000000000000000000000000000000000000000000000000),((135760137282025271696939831:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((3864859713:ℚ)/5000000000),((4043246047:ℚ)/5000000000),((-9569738141:ℚ)/13825000000),((-2904859713:ℚ)/5200000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((111616058220958059245180864162702166529932572996026043128201:ℚ)/268744949200000000000000000000000000000000000000000000000000),((9356927:ℚ)/16000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((1593864591:ℚ)/2000000000),((9042806967:ℚ)/10000000000),((-22008420901:ℚ)/28600000000),((-1478723389:ℚ)/2880000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1046942134675045648995795168408125889155915397649929757199:ℚ)/2289764505600000000000000000000000000000000000000000000000),((9356927:ℚ)/16000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((1785297983:ℚ)/2000000000),((10951812087:ℚ)/10000000000),((-27735436261:ℚ)/32400000000),((-15414277813:ℚ)/32000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1214495816477576216767790536281739:ℚ)/2430000000000000000000000000000000),((9356927:ℚ)/16000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((270917657:ℚ)/250000000),((14762352743:ℚ)/10000000000),((-39167058229:ℚ)/40000000000),((-2452094227:ℚ)/5520000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((23423776358745731375605603:ℚ)/40000000000000000000000000),((9356927:ℚ)/16000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
private theorem node0_2 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source34 nn0 nn1 Qcell ((2041:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_10
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_10
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9]
theorem packet_count : packets.length = 10 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC05
#check @N11Formalization.C450Source34GroupedC05.bound
#print axioms N11Formalization.C450Source34GroupedC05.valid0
#print axioms N11Formalization.C450Source34GroupedC05.valid1
#print axioms N11Formalization.C450Source34GroupedC05.valid2
#print axioms N11Formalization.C450Source34GroupedC05.valid3
#print axioms N11Formalization.C450Source34GroupedC05.valid4
#print axioms N11Formalization.C450Source34GroupedC05.valid5
#print axioms N11Formalization.C450Source34GroupedC05.valid6
#print axioms N11Formalization.C450Source34GroupedC05.valid7
#print axioms N11Formalization.C450Source34GroupedC05.valid8
#print axioms N11Formalization.C450Source34GroupedC05.valid9
#print axioms N11Formalization.C450Source34GroupedC05.bound
#print axioms N11Formalization.C450Source34GroupedC05.endpoint_checks
