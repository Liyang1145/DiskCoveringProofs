import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((407161351:ℚ)/625000000),((268646937:ℚ)/400000000),((-1214928559:ℚ)/3968000000),((-227161351:ℚ)/1053125000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2705119661:ℚ)/5000000000),((153842459096151648841042569741746754896543501739347233:ℚ)/678895192909240722656250000000000000000000000000000000),((325347171322919126359587:ℚ)/7220000000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((6634765931:ℚ)/10000000000),((6836324521:ℚ)/10000000000),((-31214271647:ℚ)/101100000000),((-11264297793:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((1018971173:ℚ)/2000000000),((195664330099940786408343751684018318210585492051592174183953:ℚ)/863083591406250000000000000000000000000000000000000000000000),((70895500761373318643621307:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((6754896403:ℚ)/10000000000),((6956423993:ℚ)/10000000000),((-32054967951:ℚ)/103000000000),((-11624689209:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((190428613:ℚ)/400000000),((5267050539061615552552197799640675217168706006679220968877:ℚ)/23221684931054687500000000000000000000000000000000000000000),((58415504210440456317345483:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((859372003:ℚ)/1250000000),((3508227629:ℚ)/5000000000),((-16237593403:ℚ)/52450000000),((-1498116009:ℚ)/6615625000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4403509869:ℚ)/10000000000),((426249162116796538804427338056086549651972166687166011419:ℚ)/1898314410788917541503906250000000000000000000000000000000),((716385872568109318648683:ℚ)/28880000000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((173374941:ℚ)/250000000),((3538237329:ℚ)/5000000000),((-16447661303:ℚ)/52925000000),((-101374941:ℚ)/445000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((4214427609:ℚ)/10000000000),((65478237118866638093610727403086644507140678034558563:ℚ)/291488158789062500000000000000000000000000000000000000),((24707925989864658067947:ℚ)/1155200000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-7:ℚ)/16),((-3:ℚ)/8),((437187973:ℚ)/625000000),((446030157:ℚ)/625000000),((-2082211099:ℚ)/6675000000),((-771563919:ℚ)/3367187500),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2008524549:ℚ)/5000000000),((55926074476429136470007922180763713042199346111770627:ℚ)/248858921660576015710830688476562500000000000000000000),((129667574759581162015323:ℚ)/7220000000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((3527503061:ℚ)/5000000000),((719647913:ℚ)/1000000000),((-3373535391:ℚ)/10775000000),((-6262509183:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3810079917:ℚ)/10000000000),((12153915111599982186317945327842014031968903470941199184723:ℚ)/54058743339160156250000000000000000000000000000000000000000),((6708832150554973417984827:ℚ)/462080000000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((889374201:ℚ)/1250000000),((725646481:ℚ)/1000000000),((-3415525367:ℚ)/10870000000),((-529374201:ℚ)/2284375000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((143674281:ℚ)/400000000),((4554019834189673944239275176203390338738404601419807973:ℚ)/20246584297037124633789062500000000000000000000000000000),((319592975590065156237987:ℚ)/28880000000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((7174970319:ℚ)/10000000000),((45727749:ℚ)/62500000),((-216094243:ℚ)/685312500),((-12884910957:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3360182773:ℚ)/10000000000),((8149924807185539858017406812910387689038693282260825494679:ℚ)/36217133082128906250000000000000000000000000000000000000000),((14050746026900926786976307:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((3617468269:ℚ)/5000000000),((929544881:ℚ)/1250000000),((-4426814167:ℚ)/13825000000),((-2177468269:ℚ)/9375000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((194503021:ℚ)/625000000),((7588645467720387521260598452942306521444658339468122349:ℚ)/33373385667800903320312500000000000000000000000000000000),((1906424343419214326466507:ℚ)/462080000000000000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((3677419293:ℚ)/5000000000),((7556238863:ℚ)/10000000000),((-12084557347:ℚ)/37500000000),((-6712257879:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2546881191:ℚ)/10000000000),((99811384360167590169008725881233316748397281160858474903:ℚ)/438631050000000000000000000000000000000000000000000000000),((-1322500462220315925945237:ℚ)/462080000000000000000000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-7:ℚ)/16),((-3:ℚ)/8),((3737350913:ℚ)/5000000000),((1607080329:ℚ)/2000000000),((-7921562303:ℚ)/22880000000),((-6892052739:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((1818356591:ℚ)/10000000000),((554158685763486552770198367578559329022250498213013126093:ℚ)/2305275781250000000000000000000000000000000000000000000000),((-4573319779037330824239597:ℚ)/462080000000000000000000000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((1988450901:ℚ)/2500000000),((8514070511:ℚ)/10000000000),((-42958493577:ℚ)/122000000000),((-46979663:ℚ)/200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((732666590502197004176438158706196237850890575045193:ℚ)/3050000000000000000000000000000000000000000000000000),((-88599:ℚ)/5120000)⟩
theorem valid12 : Valid source28 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((2108104697:ℚ)/2500000000),((5212615549:ℚ)/5000000000),((-9389436281:ℚ)/21600000000),((-4164314091:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((379623180121957152147241335803124161188112283762542949083:ℚ)/1350000000000000000000000000000000000000000000000000000000),((-88599:ℚ)/5120000)⟩
theorem valid13 : Valid source28 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((646463531:ℚ)/625000000),((7119142857:ℚ)/5000000000),((-41513999999:ℚ)/80000000000),((-466463531:ℚ)/2300000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((18653135562180502319573122322826225423480209734519787:ℚ)/57032812500000000000000000000000000000000000000000000),((-88599:ℚ)/5120000)⟩
theorem valid14 : Valid source28 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source28 nn0 nn1 Qcell ((1011:ℚ)/1600) ((1049:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source28 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source28 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC10
#check @N11Formalization.C450Source28GroupedC10.bound
#print axioms N11Formalization.C450Source28GroupedC10.valid0
#print axioms N11Formalization.C450Source28GroupedC10.valid1
#print axioms N11Formalization.C450Source28GroupedC10.valid2
#print axioms N11Formalization.C450Source28GroupedC10.valid3
#print axioms N11Formalization.C450Source28GroupedC10.valid4
#print axioms N11Formalization.C450Source28GroupedC10.valid5
#print axioms N11Formalization.C450Source28GroupedC10.valid6
#print axioms N11Formalization.C450Source28GroupedC10.valid7
#print axioms N11Formalization.C450Source28GroupedC10.valid8
#print axioms N11Formalization.C450Source28GroupedC10.valid9
#print axioms N11Formalization.C450Source28GroupedC10.valid10
#print axioms N11Formalization.C450Source28GroupedC10.valid11
#print axioms N11Formalization.C450Source28GroupedC10.valid12
#print axioms N11Formalization.C450Source28GroupedC10.valid13
#print axioms N11Formalization.C450Source28GroupedC10.valid14
#print axioms N11Formalization.C450Source28GroupedC10.bound
#print axioms N11Formalization.C450Source28GroupedC10.endpoint_checks
