import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/8),((-1:ℚ)/16),((3064000661:ℚ)/5000000000),((404031131:ℚ)/625000000),((275968869:ℚ)/3218750000),((8135999339:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6328993743:ℚ)/10000000000),((-401681770974838898978577230441877544032243945777501522267:ℚ)/3204683370971679687500000000000000000000000000000000000000),((-123917198877476546961202859:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((6371532341:ℚ)/10000000000),((12863077:ℚ)/19531250),((33547692:ℚ)/409765625),((16028467659:ℚ)/103000000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((180165473:ℚ)/312500000),((-284171357795370937216915000532663648161702506031394761637:ℚ)/2335774949119758605957031250000000000000000000000000000000),((-535581987578161889754344299:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((405820501:ℚ)/625000000),((3323278639:ℚ)/5000000000),((2116721361:ℚ)/26462500000),((994179499:ℚ)/6556250000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((5464802817:ℚ)/10000000000),((-7639332033740802934539866618332404843343344159683193725140489:ℚ)/63722618141362384033203125000000000000000000000000000000000000),((-2170330522524102834603179:ℚ)/14440000000000000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((655388619:ℚ)/1000000000),((3353597751:ℚ)/5000000000),((2086402249:ℚ)/26700000000),((1584611381:ℚ)/10585000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((5308966329:ℚ)/10000000000),((-7869770628779033257133850693041909275405340360912209366129529:ℚ)/66644686672896093750000000000000000000000000000000000000000000),((-5656328196641975874515819:ℚ)/36966400000000000000000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/8),((-1:ℚ)/16),((3307309453:ℚ)/5000000000),((6767810749:ℚ)/10000000000),((4112189251:ℚ)/53875000000),((2630896849:ℚ)/17800000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((5148946769:ℚ)/10000000000),((-5276874454811045807333005771478389026670616136409071721457:ℚ)/45360013368916511535644531250000000000000000000000000000000),((-143918105775064188433324411:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((6675326869:ℚ)/10000000000),((1365680729:ℚ)/2000000000),((810319271:ℚ)/10870000000),((15724673131:ℚ)/107750000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2492167733:ℚ)/5000000000),((-85462279860452849905372312152882073512794418043566732544119:ℚ)/745578188133696875000000000000000000000000000000000000000000),((-585723521275156557450779819:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((1684002689:ℚ)/2500000000),((1377794959:ℚ)/2000000000),((266068347:ℚ)/3655000000),((3915997311:ℚ)/27175000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((37614497:ℚ)/78125000),((-5091424404260922812131379023896092046070030189804158960883:ℚ)/45072460044040917968750000000000000000000000000000000000000),((-37236637967182281646493059:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((3398335611:ℚ)/5000000000),((6949524783:ℚ)/10000000000),((3930475217:ℚ)/55300000000),((7801664389:ℚ)/54825000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4639345173:ℚ)/10000000000),((-1473817706839600026232437724562073443403965248339347369454339:ℚ)/13237362141518115234375000000000000000000000000000000000000000),((-419571033262719770425619:ℚ)/2560000000000000000000000)⟩
theorem valid7 : Valid source36 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source36 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((3428654447:ℚ)/5000000000),((701005417:ℚ)/1000000000),((386994583:ℚ)/5577500000),((7771345553:ℚ)/55300000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((4457733847:ℚ)/10000000000),((-162488872528783810712054555778834256315725985217632685569:ℚ)/1480474728654837036132812500000000000000000000000000000000),((-153986675323623085244995811:ℚ)/924160000000000000000000000)⟩
theorem valid8 : Valid source36 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((3458962191:ℚ)/5000000000),((7070563499:ℚ)/10000000000),((1269812167:ℚ)/18750000000),((7741037809:ℚ)/55775000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4269011387:ℚ)/10000000000),((-130017486430146744485046608768418715964278201392107023434461:ℚ)/1201529029011726379394531250000000000000000000000000000000000),((-156511169857453182083000099:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid source36 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source36 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source36 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((6978518269:ℚ)/10000000000),((3595762027:ℚ)/5000000000),((1844237973:ℚ)/28600000000),((15421481731:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2036091459:ℚ)/5000000000),((-622829070762328711983208228100397327518867689791871390853:ℚ)/5921519175000000000000000000000000000000000000000000000000),((-636154586726262749396542619:ℚ)/3696640000000000000000000000)⟩
theorem valid10 : Valid source36 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((3549821741:ℚ)/5000000000),((74332263:ℚ)/100000000),((34467737:ℚ)/591000000),((7650178259:ℚ)/57200000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3648883297:ℚ)/10000000000),((-36474830759530197643329771947596226281192178034815297:ℚ)/366422419867968750000000000000000000000000000000000000),((-164102624475371086317757499:ℚ)/924160000000000000000000000)⟩
theorem valid11 : Valid source36 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((458853643:ℚ)/625000000),((7674660221:ℚ)/10000000000),((3205339779:ℚ)/61000000000),((941146357:ℚ)/7387500000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1307414917:ℚ)/5000000000),((-2601230866273465041372794540628234049028462331868651845117299:ℚ)/27527830090625000000000000000000000000000000000000000000000000),((-2722924696942273185675371:ℚ)/14440000000000000000000000)⟩
theorem valid12 : Valid source36 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source36 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((1516676857:ℚ)/2000000000),((2039205099:ℚ)/2500000000),((680794901:ℚ)/16200000000),((2963323143:ℚ)/24400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((10333963:ℚ)/156250000),((-1408521753658025547656987747305869162707484131059916311063:ℚ)/16479099675000000000000000000000000000000000000000000000000),((-29517025762096419973508371:ℚ)/147865600000000000000000000)⟩
theorem valid13 : Valid source36 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((8066074823:ℚ)/10000000000),((5039273409:ℚ)/5000000000),((400726591:ℚ)/40000000000),((1592658353:ℚ)/14400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-324476184972383740010922208873302919577293200473995046093:ℚ)/5400000000000000000000000000000000000000000000000000000000),((-51298001:ℚ)/256000000)⟩
theorem valid14 : Valid source36 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((4994700823:ℚ)/5000000000),((6952458577:ℚ)/5000000000),((-1512458577:ℚ)/40000000000),((6205299177:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-84409496429348328149133110029576533:ℚ)/4000000000000000000000000000000000000),((-51298001:ℚ)/256000000)⟩
theorem valid15 : Valid source36 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC15
#check @N11Formalization.C450Source36GroupedC15.bound
#print axioms N11Formalization.C450Source36GroupedC15.valid0
#print axioms N11Formalization.C450Source36GroupedC15.valid1
#print axioms N11Formalization.C450Source36GroupedC15.valid2
#print axioms N11Formalization.C450Source36GroupedC15.valid3
#print axioms N11Formalization.C450Source36GroupedC15.valid4
#print axioms N11Formalization.C450Source36GroupedC15.valid5
#print axioms N11Formalization.C450Source36GroupedC15.valid6
#print axioms N11Formalization.C450Source36GroupedC15.valid7
#print axioms N11Formalization.C450Source36GroupedC15.valid8
#print axioms N11Formalization.C450Source36GroupedC15.valid9
#print axioms N11Formalization.C450Source36GroupedC15.valid10
#print axioms N11Formalization.C450Source36GroupedC15.valid11
#print axioms N11Formalization.C450Source36GroupedC15.valid12
#print axioms N11Formalization.C450Source36GroupedC15.valid13
#print axioms N11Formalization.C450Source36GroupedC15.valid14
#print axioms N11Formalization.C450Source36GroupedC15.valid15
#print axioms N11Formalization.C450Source36GroupedC15.bound
#print axioms N11Formalization.C450Source36GroupedC15.endpoint_checks
