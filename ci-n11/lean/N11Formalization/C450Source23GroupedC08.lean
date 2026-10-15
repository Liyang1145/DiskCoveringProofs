import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((3288587337:ℚ)/5000000000),((3445625673:ℚ)/5000000000),((-24290631057:ℚ)/49600000000),((-2408587337:ℚ)/6437500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5248128667:ℚ)/10000000000),((2566605327959897203045114879488901693912844096633673199:ℚ)/12922110366821289062500000000000000000000000000000000000),((91049297167026343263551751:ℚ)/462080000000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((6816265021:ℚ)/10000000000),((7010753149:ℚ)/10000000000),((-49656778341:ℚ)/103000000000),((-5056265021:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2290696769:ℚ)/5000000000),((17478046139958145578909562946421013354556247335787188691:ℚ)/90709706761932373046875000000000000000000000000000000000),((350540251312131393591089039:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((6935766573:ℚ)/10000000000),((1414098767:ℚ)/2000000000),((-10038888903:ℚ)/20980000000),((-5175766573:ℚ)/13231250000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1052988417:ℚ)/2500000000),((720918869690087396509302385589370460805982082544604368469:ℚ)/3796628821577835083007812500000000000000000000000000000000),((343630981418885823966271791:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((6995507137:ℚ)/10000000000),((1782556989:ℚ)/2500000000),((-12683012901:ℚ)/26462500000),((-5235507137:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((4015367569:ℚ)/10000000000),((124493957520808282212856742905316951814343192861807107311:ℚ)/655848357275390625000000000000000000000000000000000000000),((340156123490365335925422551:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((7055241139:ℚ)/10000000000),((7189955689:ℚ)/10000000000),((-17089867067:ℚ)/35600000000),((-5295241139:ℚ)/13468750000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1904624119:ℚ)/5000000000),((251859240168904576237087264241389153102605483342675003:ℚ)/1327247582189738750457763671875000000000000000000000000),((932597716077342543309719:ℚ)/5120000000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((7114968753:ℚ)/10000000000),((7249677201:ℚ)/10000000000),((-51807094809:ℚ)/107750000000),((-5354968753:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1795975031:ℚ)/5000000000),((320469963019443718388223669397508451892658996103491810271:ℚ)/1689335729348754882812500000000000000000000000000000000000),((333165931809026303601131511:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((143493803:ℚ)/200000000),((3654696329:ℚ)/5000000000),((-26172266961:ℚ)/54350000000),((-108293803:ℚ)/274125000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((26260161:ℚ)/78125000),((10841389963221064867096322043148496369033523371509:ℚ)/57166826250457763671875000000000000000000000000000),((131860234708001996687711:ℚ)/739328000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((3617202747:ℚ)/5000000000),((7369102217:ℚ)/10000000000),((-17627306651:ℚ)/36550000000),((-2737202747:ℚ)/6912500000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3114329463:ℚ)/10000000000),((1117576284290651604099007715606961211801112614163095401:ℚ)/5894715670919418334960937500000000000000000000000000000),((81530433751598718571040511:ℚ)/462080000000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7294114941:ℚ)/10000000000),((7428806029:ℚ)/10000000000),((-53419254261:ℚ)/110600000000),((-5534114941:ℚ)/13943750000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((711696511:ℚ)/2500000000),((27749515678392786331390747239853947214771592945282642061:ℚ)/146407706552100181579589843750000000000000000000000000000),((322579371460557135634877199:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-9:ℚ)/16),((-1:ℚ)/2),((1838454661:ℚ)/2500000000),((7488504243:ℚ)/10000000000),((-556252971:ℚ)/1150000000),((-1398454661:ℚ)/3515625000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2552202457:ℚ)/10000000000),((1155813333932736483639344835220823032855441371257699:ℚ)/6099799065850675106048583984375000000000000000000000),((19938968194288978685928959:ℚ)/115520000000000000000000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((29654067:ℚ)/40000000),((7607884439:ℚ)/10000000000),((-18343653317:ℚ)/37500000000),((-22614067:ℚ)/57200000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((221983233:ℚ)/1000000000),((15295890820882709164291363749282317546838801467:ℚ)/79751100000000000000000000000000000000000000000),((5047265426299746280431:ℚ)/29573120000000000000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-9:ℚ)/16),((-1:ℚ)/2),((1506579347:ℚ)/2000000000),((808520751:ℚ)/1000000000),((-5932686759:ℚ)/11440000000),((-1154579347:ℚ)/3050000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((664921073:ℚ)/5000000000),((1299481095730004355607830708082826004092842993016104117:ℚ)/6339508398437500000000000000000000000000000000000000000),((12330988076497108078952111:ℚ)/73932800000000000000000000)⟩
theorem valid11 : Valid source23 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source23 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((8010219033:ℚ)/10000000000),((8562256351:ℚ)/10000000000),((-63620307159:ℚ)/122000000000),((-6250219033:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((9157753061832907234478578243426796737368448530545161229:ℚ)/45024862500000000000000000000000000000000000000000000000),((21067511:ℚ)/128000000)⟩
theorem valid12 : Valid source23 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((8487267193:ℚ)/10000000000),((1046849613:ℚ)/1000000000),((-2692548839:ℚ)/4320000000),((-6727267193:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((81897357308044777017483501339199651492230208204969970507:ℚ)/337500000000000000000000000000000000000000000000000000000),((21067511:ℚ)/128000000)⟩
theorem valid13 : Valid source23 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((5196752449:ℚ)/5000000000),((14275806401:ℚ)/10000000000),((-115042257609:ℚ)/160000000000),((-1438917483:ℚ)/4600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((242508180310554961105688019511618019478282490107399654104073:ℚ)/846400000000000000000000000000000000000000000000000000000000),((21067511:ℚ)/128000000)⟩
theorem valid14 : Valid source23 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source23 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source23 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source23 nn0 nn1 Qcell ((2117:ℚ)/3200) ((2193:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source23 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source23 nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source23 nn0 nn1 Qcell ((2193:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source23 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC08
#check @N11Formalization.C450Source23GroupedC08.bound
#print axioms N11Formalization.C450Source23GroupedC08.valid0
#print axioms N11Formalization.C450Source23GroupedC08.valid1
#print axioms N11Formalization.C450Source23GroupedC08.valid2
#print axioms N11Formalization.C450Source23GroupedC08.valid3
#print axioms N11Formalization.C450Source23GroupedC08.valid4
#print axioms N11Formalization.C450Source23GroupedC08.valid5
#print axioms N11Formalization.C450Source23GroupedC08.valid6
#print axioms N11Formalization.C450Source23GroupedC08.valid7
#print axioms N11Formalization.C450Source23GroupedC08.valid8
#print axioms N11Formalization.C450Source23GroupedC08.valid9
#print axioms N11Formalization.C450Source23GroupedC08.valid10
#print axioms N11Formalization.C450Source23GroupedC08.valid11
#print axioms N11Formalization.C450Source23GroupedC08.valid12
#print axioms N11Formalization.C450Source23GroupedC08.valid13
#print axioms N11Formalization.C450Source23GroupedC08.valid14
#print axioms N11Formalization.C450Source23GroupedC08.bound
#print axioms N11Formalization.C450Source23GroupedC08.endpoint_checks
