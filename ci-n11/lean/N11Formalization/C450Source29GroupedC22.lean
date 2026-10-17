import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((5:ℚ)/16),((3:ℚ)/8),((1423111579:ℚ)/2500000000),((3008863591:ℚ)/5000000000),((2287111579:ℚ)/5150000000),((13506590773:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((144847123:ℚ)/200000000),((-460880276907451501485932424948926559222217151937407797:ℚ)/2561078906250000000000000000000000000000000000000000000),((-168812855669693573548215243:ℚ)/462080000000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((2966610073:ℚ)/5000000000),((6258190357:ℚ)/10000000000),((4694610073:ℚ)/10680000000),((27734571071:ℚ)/51500000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((3375160743:ℚ)/5000000000),((-337110766667118211097093916614586621537180459855947557:ℚ)/1903416300000000000000000000000000000000000000000000000),((-677192214931206653465294947:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((3086878257:ℚ)/5000000000),((3189171431:ℚ)/5000000000),((4814878257:ℚ)/10870000000),((14047514293:ℚ)/26700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3113245493:ℚ)/5000000000),((-1436920629357085487753252390300616287911768337430629253:ℚ)/8027284393750000000000000000000000000000000000000000000),((-171321687103266802819284683:ℚ)/462080000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((6293943627:ℚ)/10000000000),((406152897:ℚ)/625000000),((9749943627:ℚ)/22120000000),((1778458691:ℚ)/3396875000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2974982353:ℚ)/5000000000),((-187776496978210468170265312165855667622991952089435767:ℚ)/1056952356250000000000000000000000000000000000000000000),((-2679458030145762549994427:ℚ)/7220000000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/16),((3:ℚ)/8),((1282816099:ℚ)/2000000000),((6618503367:ℚ)/10000000000),((1974016099:ℚ)/4500000000),((4116501443:ℚ)/7900000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5661767603:ℚ)/10000000000),((-1177114212784972639313980789893019033579765040198797:ℚ)/6674194335937500000000000000000000000000000000000000),((-686471225887121722332918667:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((3267084861:ℚ)/5000000000),((421157267:ℚ)/625000000),((384237297:ℚ)/880000000),((1823471801:ℚ)/3515625000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5359984029:ℚ)/10000000000),((-745913510295551107612672203069792157303084912210733:ℚ)/4259200000000000000000000000000000000000000000000000),((-2683112594446646283876467:ℚ)/7220000000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((1330842747:ℚ)/2000000000),((3429243637:ℚ)/5000000000),((2022042747:ℚ)/4652000000),((14767730911:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5042140787:ℚ)/10000000000),((-109446498299915929756686933160197227727268787997978807:ℚ)/629215098800000000000000000000000000000000000000000000),((-171789551146628781340063907:ℚ)/462080000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((1693553699:ℚ)/2500000000),((3489209217:ℚ)/5000000000),((2557553699:ℚ)/5910000000),((14947627651:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4704948859:ℚ)/10000000000),((-6192724952241597672864845051789710716771802715120111:ℚ)/35837685937500000000000000000000000000000000000000000),((-171828877670008605152527867:ℚ)/462080000000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((6894175019:ℚ)/10000000000),((3609084409:ℚ)/5000000000),((10350175019:ℚ)/24400000000),((15307253227:ℚ)/29550000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4343867733:ℚ)/10000000000),((-45720863180018465706946500767325469775472997320060571997:ℚ)/272377200000000000000000000000000000000000000000000000000),((-8946919882840173340326697:ℚ)/24320000000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((111468449:ℚ)/156250000),((769726859:ℚ)/1000000000),((165468449:ℚ)/405000000),((3205180577:ℚ)/6100000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((3520097547:ℚ)/10000000000),((-22006434687286702948228747501922408247068101299383:ℚ)/138396093750000000000000000000000000000000000000000),((-344471850689719:ℚ)/950000000000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((3806590593:ℚ)/5000000000),((4804868057:ℚ)/5000000000),((5534590593:ℚ)/16000000000),((18894604171:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-3200732587555867659621148776833915027788053194360579517:ℚ)/25600000000000000000000000000000000000000000000000000000),((-9675117:ℚ)/25600000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((9525953949:ℚ)/10000000000),((13424313337:ℚ)/10000000000),((4327317983:ℚ)/14720000000),((49232940011:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1404750460316655639617022784081904446776735520819210721:ℚ)/14950809600000000000000000000000000000000000000000000000),((-9675117:ℚ)/25600000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC22
#check @N11Formalization.C450Source29GroupedC22.bound
#print axioms N11Formalization.C450Source29GroupedC22.valid0
#print axioms N11Formalization.C450Source29GroupedC22.valid1
#print axioms N11Formalization.C450Source29GroupedC22.valid2
#print axioms N11Formalization.C450Source29GroupedC22.valid3
#print axioms N11Formalization.C450Source29GroupedC22.valid4
#print axioms N11Formalization.C450Source29GroupedC22.valid5
#print axioms N11Formalization.C450Source29GroupedC22.valid6
#print axioms N11Formalization.C450Source29GroupedC22.valid7
#print axioms N11Formalization.C450Source29GroupedC22.valid8
#print axioms N11Formalization.C450Source29GroupedC22.valid9
#print axioms N11Formalization.C450Source29GroupedC22.valid10
#print axioms N11Formalization.C450Source29GroupedC22.valid11
#print axioms N11Formalization.C450Source29GroupedC22.bound
#print axioms N11Formalization.C450Source29GroupedC22.endpoint_checks
