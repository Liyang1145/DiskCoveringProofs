import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((5525660531:ℚ)/10000000000),((3043820493:ℚ)/5000000000),((21696981593:ℚ)/35600000000),((3843820493:ℚ)/4960000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7567654063:ℚ)/10000000000),((-1410051860192379318369498066146602739:ℚ)/11279504000000000000000000000000000000),((-30310439056457520004574427:ℚ)/73932800000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((6004196781:ℚ)/10000000000),((3163389589:ℚ)/5000000000),((69397771029:ℚ)/110600000000),((1321129863:ℚ)/1780000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6599450973:ℚ)/10000000000),((-1230120137668245922345921545296147884740338410885503970389:ℚ)/8455618850000000000000000000000000000000000000000000000000),((-30432036742932766989599883:ℚ)/73932800000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((9:ℚ)/16),((5:ℚ)/8),((1248656161:ℚ)/2000000000),((6446306363:ℚ)/10000000000),((4769968483:ℚ)/7500000000),((8046306363:ℚ)/11060000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((758483949:ℚ)/1250000000),((-136016953110050467281388260671685483515766092470156601:ℚ)/878906250000000000000000000000000000000000000000000000),((-121954224749610112300146987:ℚ)/295731200000000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((198836947:ℚ)/312500000),((6565807487:ℚ)/10000000000),((2269532523:ℚ)/3575000000),((907311943:ℚ)/1250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5786381549:ℚ)/10000000000),((-4013226978567911471845757552700869708685871582595353:ℚ)/25960644531250000000000000000000000000000000000000000),((-121758974212592303047577187:ℚ)/295731200000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((6482258611:ℚ)/10000000000),((3342641921:ℚ)/5000000000),((73700327499:ℚ)/116300000000),((376603811:ℚ)/520000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((549226119:ℚ)/1000000000),((-379479381057052355213262089183166763325597986965185320059:ℚ)/2457871479687500000000000000000000000000000000000000000000),((-30388161998868655440294243:ℚ)/73932800000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((51575867:ℚ)/78125000),((3402368319:ℚ)/5000000000),((194727601:ℚ)/307812500),((4202368319:ℚ)/5815000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1295832963:ℚ)/2500000000),((-21076838217059805200489820676104025673159101530887:ℚ)/136709922552108764648437500000000000000000000000000),((-30333812722270656859615203:ℚ)/73932800000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((3360570283:ℚ)/5000000000),((3462083503:ℚ)/5000000000),((37925132547:ℚ)/60050000000),((1420694501:ℚ)/1970000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((303546147:ℚ)/625000000),((-208319057730705926487747106818817903490182068275512137963:ℚ)/1353377813281250000000000000000000000000000000000000000000),((-30276696843461421905469507:ℚ)/73932800000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((273621939:ℚ)/400000000),((3521788003:ℚ)/5000000000),((3076997451:ℚ)/4880000000),((4321788003:ℚ)/6005000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((901722439:ℚ)/2000000000),((-111605181874497845547025222223294700158565126095687411:ℚ)/726339200000000000000000000000000000000000000000000000),((-30216815411794698504840507:ℚ)/73932800000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((3479967863:ℚ)/5000000000),((7282333813:ℚ)/10000000000),((38999710767:ℚ)/62900000000),((8882333813:ℚ)/12200000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((2066741553:ℚ)/5000000000),((-56549570494478037815386676998189321816507352591596045703:ℚ)/388840920312500000000000000000000000000000000000000000000),((-6312917798846148845952873:ℚ)/15564800000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((3599326019:ℚ)/5000000000),((1880254327:ℚ)/2500000000),((13357978057:ℚ)/21600000000),((2280254327:ℚ)/3145000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((3264365131:ℚ)/10000000000),((-37606368290740682887071490311533810483268728148816179:ℚ)/259200000000000000000000000000000000000000000000000000),((-7461821058538988912867667:ℚ)/18483200000000000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((7437296507:ℚ)/10000000000),((9428450233:ℚ)/10000000000),((82295668563:ℚ)/160000000000),((11028450233:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((2072929317:ℚ)/10000000000),((-108935686089476384801441169994554797545973425244554206843:ℚ)/1600000000000000000000000000000000000000000000000000000000),((-12309119517364659:ℚ)/30400000000000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((584030293:ℚ)/625000000),((6618577503:ℚ)/5000000000),((2072090879:ℚ)/4600000000),((7418577503:ℚ)/8000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-90055292696426986063169:ℚ)/10580000000000000000000000),((-208278081:ℚ)/512000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source26 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source26 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC26
#check @N11Formalization.C450Source26GroupedC26.bound
#print axioms N11Formalization.C450Source26GroupedC26.valid0
#print axioms N11Formalization.C450Source26GroupedC26.valid1
#print axioms N11Formalization.C450Source26GroupedC26.valid2
#print axioms N11Formalization.C450Source26GroupedC26.valid3
#print axioms N11Formalization.C450Source26GroupedC26.valid4
#print axioms N11Formalization.C450Source26GroupedC26.valid5
#print axioms N11Formalization.C450Source26GroupedC26.valid6
#print axioms N11Formalization.C450Source26GroupedC26.valid7
#print axioms N11Formalization.C450Source26GroupedC26.valid8
#print axioms N11Formalization.C450Source26GroupedC26.valid9
#print axioms N11Formalization.C450Source26GroupedC26.valid10
#print axioms N11Formalization.C450Source26GroupedC26.valid11
#print axioms N11Formalization.C450Source26GroupedC26.bound
#print axioms N11Formalization.C450Source26GroupedC26.endpoint_checks
