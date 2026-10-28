import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((5936421721:ℚ)/10000000000),((6478583939:ℚ)/10000000000),((30609265163:ℚ)/106800000000),((9838583939:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((134871553:ℚ)/200000000),((368044727462664110821358556225353511719:ℚ)/4384558656000000000000000000000000000000),((-36402296129105578403099913:ℚ)/115520000000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((6415264143:ℚ)/10000000000),((6717689297:ℚ)/10000000000),((4577970347:ℚ)/15800000000),((10077689297:ℚ)/26700000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((11317727:ℚ)/20000000),((85269952861964860233061451209441244791565396053796308969283:ℚ)/1113676980778125000000000000000000000000000000000000000000000),((-38235710467445953878537377:ℚ)/115520000000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((3327242569:ℚ)/5000000000),((6837200913:ℚ)/10000000000),((16381727707:ℚ)/56250000000),((10197200913:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5041401563:ℚ)/10000000000),((56190185653426886039003031415797529526007802190657449663:ℚ)/764403043359375000000000000000000000000000000000000000000),((-117446586247954525915446371:ℚ)/346560000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((26461139:ℚ)/39062500),((3478343497:ℚ)/5000000000),((129383417:ℚ)/446875000),((5158343497:ℚ)/14062500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2352711281:ℚ)/5000000000),((12987758095934034018413848413867002760038680253325449549921:ℚ)/177709114551544189453125000000000000000000000000000000000000),((-9887919651796145985741777:ℚ)/28880000000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((6893590639:ℚ)/10000000000),((884518601:ℚ)/1250000000),((33480771917:ℚ)/116300000000),((1304518601:ℚ)/3575000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2172847211:ℚ)/5000000000),((10532236693076990426658263167303219678828866667022607539699:ℚ)/144843447428576660156250000000000000000000000000000000000000),((-624258995140728072331853:ℚ)/1805000000000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((7013103663:ℚ)/10000000000),((7195587539:ℚ)/10000000000),((33839310989:ℚ)/118200000000),((10555587539:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((791141433:ℚ)/2000000000),((53950917347575591987810265979275678690308656432366302388643:ℚ)/745215111368688964843750000000000000000000000000000000000000),((-40351559130791899445262313:ℚ)/115520000000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((7132591927:ℚ)/10000000000),((7315004293:ℚ)/10000000000),((34197775781:ℚ)/120100000000),((10675004293:ℚ)/29550000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1762696893:ℚ)/5000000000),((25166810195508335436656282028245398209356601372148964995708927:ℚ)/348923119729067578125000000000000000000000000000000000000000000),((-40748634357380640250774297:ℚ)/115520000000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((3626028311:ℚ)/5000000000),((7434400111:ℚ)/10000000000),((17278084933:ℚ)/61000000000),((10794400111:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1518810133:ℚ)/5000000000),((371007275778677366770203251201760763899142766200501972427:ℚ)/5159752913134765625000000000000000000000000000000000000000),((-41143806447660869122919713:ℚ)/115520000000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((368574943:ℚ)/500000000),((7673132767:ℚ)/10000000000),((1745724829:ℚ)/6290000000),((11033132767:ℚ)/30500000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((2458366099:ℚ)/10000000000),((643679404770575221100562575872177298148899218962729262702071:ℚ)/8769823224707031250000000000000000000000000000000000000000000),((-1091902911224949:ℚ)/3040000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((1902580021:ℚ)/2500000000),((7911792607:ℚ)/10000000000),((8907740063:ℚ)/32400000000),((11271792607:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((46617739500610967561305667086919661720875824066256903724359:ℚ)/637796319542578125000000000000000000000000000000000000000000),((-5881363:ℚ)/16000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((3924531609:ℚ)/5000000000),((9819077191:ℚ)/10000000000),((18173594827:ℚ)/80000000000),((13179077191:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1796553575582899369980913044085001733141787461323455069:ℚ)/19929037500000000000000000000000000000000000000000000000),((-5881363:ℚ)/16000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((4878435059:ℚ)/5000000000),((1703451081:ℚ)/1250000000),((21035305177:ℚ)/110400000000),((2123451081:ℚ)/5000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((8703245583336693724573543422221344229:ℚ)/74390625000000000000000000000000000000),((-5881363:ℚ)/16000000)⟩
theorem valid11 : Valid source22 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source22 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC20
#check @N11Formalization.C450Source22GroupedC20.bound
#print axioms N11Formalization.C450Source22GroupedC20.valid0
#print axioms N11Formalization.C450Source22GroupedC20.valid1
#print axioms N11Formalization.C450Source22GroupedC20.valid2
#print axioms N11Formalization.C450Source22GroupedC20.valid3
#print axioms N11Formalization.C450Source22GroupedC20.valid4
#print axioms N11Formalization.C450Source22GroupedC20.valid5
#print axioms N11Formalization.C450Source22GroupedC20.valid6
#print axioms N11Formalization.C450Source22GroupedC20.valid7
#print axioms N11Formalization.C450Source22GroupedC20.valid8
#print axioms N11Formalization.C450Source22GroupedC20.valid9
#print axioms N11Formalization.C450Source22GroupedC20.valid10
#print axioms N11Formalization.C450Source22GroupedC20.valid11
#print axioms N11Formalization.C450Source22GroupedC20.bound
#print axioms N11Formalization.C450Source22GroupedC20.endpoint_checks
