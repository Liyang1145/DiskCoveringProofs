import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((3231897727:ℚ)/5000000000),((3335028199:ℚ)/5000000000),((-5365084597:ℚ)/24800000000),((-1311897727:ℚ)/10110000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((1384655711:ℚ)/2500000000),((195855952709815671454151250313500694545311:ℚ)/1299200286336000000000000000000000000000000),((19233493046066666204738363:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((6584429587:ℚ)/10000000000),((1697663759:ℚ)/2500000000),((-2772991277:ℚ)/12637500000),((-2744429587:ℚ)/20600000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((2614522689:ℚ)/5000000000),((141015298594916870793543113791402392814199768968179217499:ℚ)/929341819557952880859375000000000000000000000000000000000),((55266141782273900804008243:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((6704992607:ℚ)/10000000000),((6911185193:ℚ)/10000000000),((-11453555579:ℚ)/51500000000),((-2864992607:ℚ)/20980000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2451030231:ℚ)/5000000000),((560320256522699905896783252447023546348221269325160079933593:ℚ)/3669549205099487304687500000000000000000000000000000000000000),((33417518378774447366084603:ℚ)/2957312000000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((1365097699:ℚ)/2000000000),((3485712889:ℚ)/5000000000),((-5817138667:ℚ)/26225000000),((-597097699:ℚ)/4234000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((142308649:ℚ)/312500000),((1049427348078507817724440362662800335065995596626582736379153:ℚ)/6920625742583691406250000000000000000000000000000000000000000),((455508534729390481889747:ℚ)/118292480000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((3442856213:ℚ)/5000000000),((7031650631:ℚ)/10000000000),((-11814951893:ℚ)/52925000000),((-1522856213:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((4370250819:ℚ)/10000000000),((279102933917790078752730882064085293731909077217582418927751:ℚ)/1834774262465161132812500000000000000000000000000000000000000),((76188627774882314215843:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/8),((-5:ℚ)/16),((868240117:ℚ)/1250000000),((3545930091:ℚ)/5000000000),((-5997790273:ℚ)/26700000000),((-388240117:ℚ)/2693750000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2089577099:ℚ)/5000000000),((374680662791424763689141234427714966063857681564228669676459:ℚ)/2455420245168750000000000000000000000000000000000000000000000),((-169119261845956136665117:ℚ)/46208000000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((3503057221:ℚ)/5000000000),((7152054841:ℚ)/10000000000),((-12176164523:ℚ)/53875000000),((-1583057221:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3979505221:ℚ)/10000000000),((176754322289164044261626267987437609208909614708211829257961041:ℚ)/1154784524082995605468750000000000000000000000000000000000000000),((-5499372233274781419702973:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((141325867:ℚ)/200000000),((28172793:ℚ)/39062500),((-96536758:ℚ)/424609375),((-64525867:ℚ)/438600000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3769939577:ℚ)/10000000000),((314019874228030845532147980330605563698350992953712272677:ℚ)/2045377595867463946342468261718750000000000000000000000000),((-13286741519209430449117:ℚ)/1182924800000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((111350907:ℚ)/156250000),((909050133:ℚ)/1250000000),((-1567150399:ℚ)/6853125000),((-51350907:ℚ)/345625000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((8871737:ℚ)/25000000),((244773998371933588170096416451735353402621024745673759639:ℚ)/1589590560054588317871093750000000000000000000000000000000),((-10859805925166381103997:ℚ)/722000000000000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((3593304457:ℚ)/5000000000),((1848173079:ℚ)/2500000000),((-3224519237:ℚ)/13825000000),((-1673304457:ℚ)/11250000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1656712921:ℚ)/5000000000),((1422346029157066400347766889376532023555990449294989093:ℚ)/9100036230468750000000000000000000000000000000000000000),((-13948064957748905672320597:ℚ)/739328000000000000000000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((3653435291:ℚ)/5000000000),((1502586281:ℚ)/2000000000),((-2651758843:ℚ)/11250000000),((-1733435291:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1393200971:ℚ)/5000000000),((39229848486009104716425718717510508721793394603883921129:ℚ)/249621582031250000000000000000000000000000000000000000000),((-19637534761869353004106493:ℚ)/739328000000000000000000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((7427081107:ℚ)/10000000000),((3996708003:ℚ)/5000000000),((-7350124009:ℚ)/28600000000),((-3587081107:ℚ)/24400000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((1068627451:ℚ)/5000000000),((22937005638469341629406457359482664331007584182699004504147:ℚ)/136012178087500000000000000000000000000000000000000000000000),((-101490760156973638973032397:ℚ)/2957312000000000000000000000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((158149213:ℚ)/200000000),((338929899:ℚ)/400000000),((-645589697:ℚ)/2440000000),((-81349213:ℚ)/518400000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((8493634522956491497651037495326212639261010178252095553:ℚ)/49640744700000000000000000000000000000000000000000000000),((-46685419:ℚ)/1024000000)⟩
theorem valid12 : Valid source31 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((4193599879:ℚ)/5000000000),((10387932383:ℚ)/10000000000),((-21883797149:ℚ)/64800000000),((-2273599879:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((823994289872135868568252295998961895420516772627169189:ℚ)/3936600000000000000000000000000000000000000000000000000),((-46685419:ℚ)/1024000000)⟩
theorem valid13 : Valid source31 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((10301604899:ℚ)/10000000000),((14205089969:ℚ)/10000000000),((-33335269907:ℚ)/80000000000),((-6461604899:ℚ)/44160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((52764130866270358649736593805426519260441:ℚ)/203136000000000000000000000000000000000000),((-46685419:ℚ)/1024000000)⟩
theorem valid14 : Valid source31 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source31 nn0 nn1 Qcell ((1011:ℚ)/1600) ((1049:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source31 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source31 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC11
#check @N11Formalization.C450Source31GroupedC11.bound
#print axioms N11Formalization.C450Source31GroupedC11.valid0
#print axioms N11Formalization.C450Source31GroupedC11.valid1
#print axioms N11Formalization.C450Source31GroupedC11.valid2
#print axioms N11Formalization.C450Source31GroupedC11.valid3
#print axioms N11Formalization.C450Source31GroupedC11.valid4
#print axioms N11Formalization.C450Source31GroupedC11.valid5
#print axioms N11Formalization.C450Source31GroupedC11.valid6
#print axioms N11Formalization.C450Source31GroupedC11.valid7
#print axioms N11Formalization.C450Source31GroupedC11.valid8
#print axioms N11Formalization.C450Source31GroupedC11.valid9
#print axioms N11Formalization.C450Source31GroupedC11.valid10
#print axioms N11Formalization.C450Source31GroupedC11.valid11
#print axioms N11Formalization.C450Source31GroupedC11.valid12
#print axioms N11Formalization.C450Source31GroupedC11.valid13
#print axioms N11Formalization.C450Source31GroupedC11.valid14
#print axioms N11Formalization.C450Source31GroupedC11.bound
#print axioms N11Formalization.C450Source31GroupedC11.endpoint_checks
