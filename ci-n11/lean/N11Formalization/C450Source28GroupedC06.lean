import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((6796616953:ℚ)/10000000000),((3506194491:ℚ)/5000000000),((-30248139401:ℚ)/49600000000),((-5068616953:ℚ)/10110000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4639504749:ℚ)/10000000000),((75831447086048549375140459216562612771220624537383717849975617:ℚ)/259840057267200000000000000000000000000000000000000000000000000),((6206530037985229652331807819:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((3458189331:ℚ)/5000000000),((1768055583:ℚ)/2500000000),((-15288611413:ℚ)/25275000000),((-2594189331:ℚ)/5102500000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((2136960391:ℚ)/5000000000),((75510433854554525956873791265700170173727249291953764741303:ℚ)/262735971662866882324218750000000000000000000000000000000000),((1541584555085979878480627251:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((1744061303:ℚ)/2500000000),((713204713:ℚ)/1000000000),((-475480911:ℚ)/785000000),((-1312061303:ℚ)/2575000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((509965991:ℚ)/1250000000),((9226487259964290641677218849976093060514707805060660181:ℚ)/32074761591406250000000000000000000000000000000000000000),((384126120068419031735605419:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((879512823:ℚ)/1250000000),((3580978199:ℚ)/5000000000),((-31070760189:ℚ)/51500000000),((-663512823:ℚ)/1293437500),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((3876420013:ℚ)/10000000000),((41756644655344190717832032044723278415107213997849155423054951:ℚ)/146248882830992187500000000000000000000000000000000000000000000),((95711687540182117146957739:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7066027909:ℚ)/10000000000),((112372869:ℚ)/156250000),((-976101559:ℚ)/1616796875),((-5338027909:ℚ)/10395000000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((3770888223:ℚ)/10000000000),((1976554109674766701770746046641335819460417040838978427471:ℚ)/6919447763058366626501083374023437500000000000000000000000),((6115256930215697781326520771:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((3547975517:ℚ)/5000000000),((7221768813:ℚ)/10000000000),((-62799456943:ℚ)/103950000000),((-2683975517:ℚ)/5221250000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((915618559:ℚ)/2500000000),((795551263147957312500643036771452088538032950310828901238556207:ℚ)/2783747066537230664062500000000000000000000000000000000000000000),((1526232111625047012061974099:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((712587199:ℚ)/1000000000),((7251672017:ℚ)/10000000000),((-63128392187:ℚ)/104425000000),((-539787199:ℚ)/1049000000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((443864177:ℚ)/1250000000),((559784561223357681750445622929726542270987276678845209163020713:ℚ)/1957872715602696118164062500000000000000000000000000000000000000),((60945625490838390597576891:ℚ)/147865600000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-11:ℚ)/16),((-5:ℚ)/8),((7155790807:ℚ)/10000000000),((1456314651:ℚ)/2000000000),((-12691461161:ℚ)/20980000000),((-5427790807:ℚ)/10537500000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((3435898587:ℚ)/10000000000),((39107664710462476076006992973116845512112703767120234395777:ℚ)/136719469148533500000000000000000000000000000000000000000000),((6084159235814963158752036459:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((1437141503:ℚ)/2000000000),((1462294511:ℚ)/2000000000),((-4252413207:ℚ)/7025000000),((-1091541503:ℚ)/2117000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((3317069791:ℚ)/10000000000),((2778973074071104802328300381745009338899745577498984290671253:ℚ)/9710927664184472656250000000000000000000000000000000000000000),((242948740175529834184994619:ℚ)/591462400000000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((3607811071:ℚ)/5000000000),((3670684971:ℚ)/5000000000),((-32057534681:ℚ)/52925000000),((-2743811071:ℚ)/5316250000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((1597000337:ℚ)/5000000000),((4798065744776849825112000405210796299206550180933711542997001811:ℚ)/16759203823980909863281250000000000000000000000000000000000000000),((1515810088261646273833775931:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((1811383679:ℚ)/2500000000),((3685632721:ℚ)/5000000000),((-32221959931:ℚ)/53162500000),((-1379383679:ℚ)/2670000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((3066179963:ℚ)/10000000000),((1597852272695032002063214383975166286178501212940329193316547:ℚ)/5578757467676852416992187500000000000000000000000000000000000),((378295298743094138895503931:ℚ)/924160000000000000000000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-11:ℚ)/16),((-5:ℚ)/8),((3637722633:ℚ)/5000000000),((1857762721:ℚ)/2500000000),((-5425129977:ℚ)/8900000000),((-2773722633:ℚ)/5387500000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((586597147:ℚ)/2000000000),((923408712420128595891166042805216110694739058112400920067:ℚ)/3197161777563476562500000000000000000000000000000000000000),((1510542945629932649811075499:ℚ)/3696640000000000000000000000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((7335260399:ℚ)/10000000000),((3745414539:ℚ)/5000000000),((-32879559929:ℚ)/53875000000),((-5607260399:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((661799577:ℚ)/2500000000),((333772031628088824486264320827323575199850065453799605750416219:ℚ)/1154784524082995605468750000000000000000000000000000000000000000),((6020953508726946652362094491:ℚ)/14786560000000000000000000000)⟩
theorem valid12 : Valid source28 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source28 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((1848766939:ℚ)/2500000000),((7610364481:ℚ)/10000000000),((-67074009291:ℚ)/108700000000),((-202395277:ℚ)/395000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1163761813:ℚ)/5000000000),((229898360921720962828839723667920484694216401665236307712881:ℚ)/782785654709277343750000000000000000000000000000000000000000),((374974094731346873930375811:ℚ)/924160000000000000000000000)⟩
theorem valid13 : Valid source28 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((7514659949:ℚ)/10000000000),((7849356287:ℚ)/10000000000),((-69702919157:ℚ)/110600000000),((-5786659949:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((300000429:ℚ)/2000000000),((4025511082537418384682884097860893204015544243671288033585051:ℚ)/13300688451050000000000000000000000000000000000000000000000000),((5956400316359047714787523891:ℚ)/14786560000000000000000000000)⟩
theorem valid14 : Valid source28 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((3876879783:ℚ)/5000000000),((2201110461:ℚ)/2500000000),((-20052215071:ℚ)/28600000000),((-1004293261:ℚ)/2160000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((320334953623524062759688159286401647172588574858245553553:ℚ)/911002950000000000000000000000000000000000000000000000000),((410333169:ℚ)/1024000000)⟩
theorem valid15 : Valid source28 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((4354606059:ℚ)/5000000000),((2677924469:ℚ)/2500000000),((-25297169159:ℚ)/32400000000),((-3490606059:ℚ)/8000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((256569213512603532986303855775379361767677196756341859463:ℚ)/637729200000000000000000000000000000000000000000000000000),((410333169:ℚ)/1024000000)⟩
theorem valid16 : Valid source28 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((2654247629:ℚ)/2500000000),((14520195973:ℚ)/10000000000),((-143082155703:ℚ)/160000000000),((-2222247629:ℚ)/5520000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((794728689203435288164078991468801679357293:ℚ)/1625088000000000000000000000000000000000000),((410333169:ℚ)/1024000000)⟩
theorem valid17 : Valid source28 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source28 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4139:ℚ)/6400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((4139:ℚ)/6400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source28 nn0 nn1 Qcell ((4139:ℚ)/6400) ((4177:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source28 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source28 nn0 nn1 Qcell ((4177:ℚ)/6400) ((2117:ℚ)/3200) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source28 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2117:ℚ)/3200) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source28 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source28 nn0 nn1 Qcell ((2117:ℚ)/3200) ((1087:ℚ)/1600) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source28 nn0 nn1 Qcell ((2117:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC06
#check @N11Formalization.C450Source28GroupedC06.bound
#print axioms N11Formalization.C450Source28GroupedC06.valid0
#print axioms N11Formalization.C450Source28GroupedC06.valid1
#print axioms N11Formalization.C450Source28GroupedC06.valid2
#print axioms N11Formalization.C450Source28GroupedC06.valid3
#print axioms N11Formalization.C450Source28GroupedC06.valid4
#print axioms N11Formalization.C450Source28GroupedC06.valid5
#print axioms N11Formalization.C450Source28GroupedC06.valid6
#print axioms N11Formalization.C450Source28GroupedC06.valid7
#print axioms N11Formalization.C450Source28GroupedC06.valid8
#print axioms N11Formalization.C450Source28GroupedC06.valid9
#print axioms N11Formalization.C450Source28GroupedC06.valid10
#print axioms N11Formalization.C450Source28GroupedC06.valid11
#print axioms N11Formalization.C450Source28GroupedC06.valid12
#print axioms N11Formalization.C450Source28GroupedC06.valid13
#print axioms N11Formalization.C450Source28GroupedC06.valid14
#print axioms N11Formalization.C450Source28GroupedC06.valid15
#print axioms N11Formalization.C450Source28GroupedC06.valid16
#print axioms N11Formalization.C450Source28GroupedC06.valid17
#print axioms N11Formalization.C450Source28GroupedC06.bound
#print axioms N11Formalization.C450Source28GroupedC06.endpoint_checks
