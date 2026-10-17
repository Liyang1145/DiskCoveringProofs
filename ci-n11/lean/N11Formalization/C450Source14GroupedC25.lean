import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((73657191:ℚ)/125000000),((802755451:ℚ)/1250000000),((28552397:ℚ)/55625000),((8264799059:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1367089727:ℚ)/2000000000),((-125116488468886673355370081:ℚ)/43027893066406250000000000000),((-50342632964205983253639:ℚ)/225625000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6368639633:ℚ)/10000000000),((3329994793:ℚ)/5000000000),((1046948519:ℚ)/1975000000),((34129953137:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5772273727:ℚ)/10000000000),((-966634586840718750894333211042056880500715481347547:ℚ)/144445019531250000000000000000000000000000000000000000),((-814465762839577682782611:ℚ)/3610000000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/2),((9:ℚ)/16),((6606616789:ℚ)/10000000000),((3389475623:ℚ)/5000000000),((7566616789:ℚ)/14062500000),((34665280607:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((517028789:ℚ)/1000000000),((-48611365848354134017817188070027973234547776453012857:ℚ)/5793571472167968750000000000000000000000000000000000000),((-818954291438001846723531:ℚ)/3610000000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((1681398311:ℚ)/2500000000),((3448952929:ℚ)/5000000000),((1921398311:ℚ)/3575000000),((35200576361:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((605521569:ℚ)/1250000000),((-221122621416023583417342149793140468824801463294819:ℚ)/25960644531250000000000000000000000000000000000000000),((-821154668687233020347349:ℚ)/3610000000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((1711140539:ℚ)/2500000000),((7016853767:ℚ)/10000000000),((1951140539:ℚ)/3634375000),((71471683903:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4496477029:ℚ)/10000000000),((-1942118951575456839346158977800321510632329618539607:ℚ)/225024854707717895507812500000000000000000000000000000),((-173337560654656053234159:ℚ)/760000000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/2),((9:ℚ)/16),((870440487:ℚ)/1250000000),((7076325311:ℚ)/10000000000),((990440487:ℚ)/1832031250),((72006927799:ℚ)/116300000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2060856713:ℚ)/5000000000),((-13728097883010477247721203680137445677311687677:ℚ)/1463247463107109069824218750000000000000000000000),((-3302380463433672383941869:ℚ)/14440000000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((3511501093:ℚ)/5000000000),((7135795299:ℚ)/10000000000),((3991501093:ℚ)/7387500000),((72542157691:ℚ)/117250000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((78435381:ℚ)/200000000),((-1978158059585761156571343793951358662891472394794761:ℚ)/209986441040039062500000000000000000000000000000000000),((-3306773758656472408376389:ℚ)/14440000000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((7082478811:ℚ)/10000000000),((899407971:ℚ)/1250000000),((8042478811:ℚ)/14893750000),((9134671739:ℚ)/14775000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((57994671:ℚ)/156250000),((-585760286004427789781539069916262333470787361083670063:ℚ)/61946026094055175781250000000000000000000000000000000000),((-413895679754661504678017:ℚ)/1805000000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((1785488453:ℚ)/2500000000),((1813682689:ℚ)/2500000000),((2025488453:ℚ)/3753125000),((18403144201:ℚ)/29787500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3489543081:ℚ)/10000000000),((-195950690694945958296961978001884803813634278949147:ℚ)/20650906574726104736328125000000000000000000000000000),((-207222219045344065346619:ℚ)/902500000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((3600713613:ℚ)/5000000000),((914274537:ℚ)/1250000000),((1360237871:ℚ)/2521875000),((9268470833:ℚ)/15012500000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((813239653:ℚ)/2500000000),((-106019585773994354243254241460941829360110709669809:ℚ)/11138024711608886718750000000000000000000000000000000),((-207496497598415759281939:ℚ)/902500000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((7260899093:ℚ)/10000000000),((7373660423:ℚ)/10000000000),((8220899093:ℚ)/15250000000),((74682943807:ℚ)/121050000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((46851217:ℚ)/156250000),((-211597759224756048021942264766589714036827110064458347:ℚ)/22166113281250000000000000000000000000000000000000000000),((-3324330811659322082160981:ℚ)/14440000000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((7320369447:ℚ)/10000000000),((936573071:ℚ)/1250000000),((394303307:ℚ)/737500000),((9469157639:ℚ)/15250000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((680269809:ℚ)/2500000000),((-5614159393252327889340825586744314278372925320013:ℚ)/626766967773437500000000000000000000000000000000000),((-416066099296013686510917:ℚ)/1805000000000000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((3719652879:ℚ)/5000000000),((7611503441:ℚ)/10000000000),((4199652879:ℚ)/7862500000),((76823530969:ℚ)/123900000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((515011087:ℚ)/2500000000),((-26731150519357517926128199784558809941642445260321:ℚ)/2966620790958404541015625000000000000000000000000000),((-28103818364575959:ℚ)/121600000000000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((1889559107:ℚ)/2500000000),((7849326303:ℚ)/10000000000),((2129559107:ℚ)/4050000000),((78963936727:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((262208103:ℚ)/2500000000),((-121655384668532288451671414026549654171374435441271:ℚ)/15377343750000000000000000000000000000000000000000000),((-14090398744752747:ℚ)/60800000000000000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((3898040921:ℚ)/5000000000),((9751356267:ℚ)/10000000000),((4378040921:ℚ)/10000000000),((96082206403:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((89152689020681276306672987467499:ℚ)/23437500000000000000000000000000000),((-7423113:ℚ)/32000000)⟩
theorem valid14 : Valid source14 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((1939650707:ℚ)/2000000000),((847108607:ℚ)/625000000),((2131650707:ℚ)/5520000000),((8143977463:ℚ)/10000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((4525137895010541220649:ℚ)/317400000000000000000000),((-7423113:ℚ)/32000000)⟩
theorem valid15 : Valid source14 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source14 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((2383:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((2383:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source14 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source14 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source14 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source14 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source14 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source14 nn0 nn1 Qcell ((2383:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC25
#check @N11Formalization.C450Source14GroupedC25.bound
#print axioms N11Formalization.C450Source14GroupedC25.valid0
#print axioms N11Formalization.C450Source14GroupedC25.valid1
#print axioms N11Formalization.C450Source14GroupedC25.valid2
#print axioms N11Formalization.C450Source14GroupedC25.valid3
#print axioms N11Formalization.C450Source14GroupedC25.valid4
#print axioms N11Formalization.C450Source14GroupedC25.valid5
#print axioms N11Formalization.C450Source14GroupedC25.valid6
#print axioms N11Formalization.C450Source14GroupedC25.valid7
#print axioms N11Formalization.C450Source14GroupedC25.valid8
#print axioms N11Formalization.C450Source14GroupedC25.valid9
#print axioms N11Formalization.C450Source14GroupedC25.valid10
#print axioms N11Formalization.C450Source14GroupedC25.valid11
#print axioms N11Formalization.C450Source14GroupedC25.valid12
#print axioms N11Formalization.C450Source14GroupedC25.valid13
#print axioms N11Formalization.C450Source14GroupedC25.valid14
#print axioms N11Formalization.C450Source14GroupedC25.valid15
#print axioms N11Formalization.C450Source14GroupedC25.bound
#print axioms N11Formalization.C450Source14GroupedC25.endpoint_checks
