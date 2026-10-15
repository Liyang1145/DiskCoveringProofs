import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((6958428601:ℚ)/10000000000),((7198925887:ℚ)/10000000000),((-57428184757:ℚ)/99200000000),((-4718428601:ℚ)/10110000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((413841727:ℚ)/1000000000),((9445907067379587463432834739988024539:ℚ)/24601600000000000000000000000000000000),((1828024892360960076742064311:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((7078924589:ℚ)/10000000000),((7319213973:ℚ)/10000000000),((-58751353703:ℚ)/101100000000),((-4838924589:ℚ)/10300000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((3724531457:ℚ)/10000000000),((3264271665918153463832041383210147029:ℚ)/8517675000000000000000000000000000000),((1812467460438217630946855231:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((1799838697:ℚ)/2500000000),((737933653:ℚ)/1000000000),((-5941270183:ℚ)/10300000000),((-1239838697:ℚ)/2598750000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((163074017:ℚ)/500000000),((50201944500878224262566898305336277:ℚ)/132612500000000000000000000000000000),((112291730813280760562211799:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((58076371:ℚ)/80000000),((3719722647:ℚ)/5000000000),((-4290992731:ℚ)/7425000000),((-40156371:ℚ)/83920000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((600899581:ℚ)/2000000000),((26071752319139754409130620883044991:ℚ)/68913281250000000000000000000000000),((114475322082298497145151:ℚ)/236584960000000000000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((7319722871:ℚ)/10000000000),((1511924591:ℚ)/2000000000),((-12279170501:ℚ)/20980000000),((-1693240957:ℚ)/3560000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((2724242907:ℚ)/10000000000),((210224407181137160837246578466873713:ℚ)/550200500000000000000000000000000000),((1780625507698696846862128151:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((7440032243:ℚ)/10000000000),((7799828611:ℚ)/10000000000),((-64038114721:ℚ)/106800000000),((-742861749:ℚ)/1580000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((205536593:ℚ)/1000000000),((154238319077415793410487709082307031:ℚ)/396050000000000000000000000000000000),((1764340827881751647918221439:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((384024363:ℚ)/500000000),((8039851643:ℚ)/10000000000),((-66678368073:ℚ)/110600000000),((-20924951:ℚ)/44000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((1697258524166776203619027842824154911:ℚ)/4368700000000000000000000000000000000),((120657931:ℚ)/256000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((7920742533:ℚ)/10000000000),((4499222321:ℚ)/5000000000),((-38611445531:ℚ)/57200000000),((-5680742533:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((10590606930358483771781211197086017161:ℚ)/24538800000000000000000000000000000000),((120657931:ℚ)/256000000)⟩
theorem valid7 : Valid source36 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((888012453:ℚ)/1000000000),((10910686081:ℚ)/10000000000),((-98257546891:ℚ)/129600000000),((-664012453:ℚ)/1600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((558084878216500261524859682357795447:ℚ)/1166400000000000000000000000000000000),((120657931:ℚ)/256000000)⟩
theorem valid8 : Valid source36 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((5396742651:ℚ)/5000000000),((7362500001:ℚ)/5000000000),((-70107500011:ℚ)/80000000000),((-4276742651:ℚ)/11040000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((927848890121852391148505733:ℚ)/1600000000000000000000000000),((120657931:ℚ)/256000000)⟩
theorem valid9 : Valid source36 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet9 valid9
private theorem node0_2 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source36 nn0 nn1 Qcell ((2079:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_10
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_10
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9]
theorem packet_count : packets.length = 10 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC06
#check @N11Formalization.C450Source36GroupedC06.bound
#print axioms N11Formalization.C450Source36GroupedC06.valid0
#print axioms N11Formalization.C450Source36GroupedC06.valid1
#print axioms N11Formalization.C450Source36GroupedC06.valid2
#print axioms N11Formalization.C450Source36GroupedC06.valid3
#print axioms N11Formalization.C450Source36GroupedC06.valid4
#print axioms N11Formalization.C450Source36GroupedC06.valid5
#print axioms N11Formalization.C450Source36GroupedC06.valid6
#print axioms N11Formalization.C450Source36GroupedC06.valid7
#print axioms N11Formalization.C450Source36GroupedC06.valid8
#print axioms N11Formalization.C450Source36GroupedC06.valid9
#print axioms N11Formalization.C450Source36GroupedC06.bound
#print axioms N11Formalization.C450Source36GroupedC06.endpoint_checks
