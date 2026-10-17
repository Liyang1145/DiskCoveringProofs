import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((5668468203:ℚ)/10000000000),((49742863:ℚ)/80000000),((63176213827:ℚ)/106800000000),((59982863:ℚ)/79360000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((911230897:ℚ)/1250000000),((-270126517490654430021498031359612163:ℚ)/11279504000000000000000000000000000000),((-349707176768191975837197:ℚ)/946339840000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((3072861153:ℚ)/5000000000),((645638063:ℚ)/1000000000),((4819392911:ℚ)/7900000000),((773638063:ℚ)/1068000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3144732943:ℚ)/5000000000),((-108431143052504342437133572294347050406442956043111791:ℚ)/3081493750000000000000000000000000000000000000000000000),((-54975662971884398704385997:ℚ)/147865600000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((1276846487:ℚ)/2000000000),((669483503:ℚ)/1000000000),((13923618383:ℚ)/22880000000),((797483503:ℚ)/1106000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((17920523:ℚ)/31250000),((-2676172286146946468092681775603969026940410113481553383:ℚ)/74859699200000000000000000000000000000000000000000000000),((-55013528077649401729117517:ℚ)/147865600000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((6622675057:ℚ)/10000000000),((6814038707:ℚ)/10000000000),((71764075513:ℚ)/116300000000),((8094038707:ℚ)/11440000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5127379919:ℚ)/10000000000),((-99513164082176448123533118479254586354027478510351570297:ℚ)/2457871479687500000000000000000000000000000000000000000000),((-5517242462763693501114912437:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((6741873137:ℚ)/10000000000),((3466613859:ℚ)/5000000000),((72836858233:ℚ)/118200000000),((4106613859:ℚ)/5815000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1199492907:ℚ)/2500000000),((-104662889875309895631843188530257733963152038612075654153:ℚ)/2580313387500000000000000000000000000000000000000000000000),((-72612748527356270010589687:ℚ)/194560000000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((1715264183:ℚ)/2500000000),((7052402763:ℚ)/10000000000),((18477377647:ℚ)/30025000000),((8332402763:ℚ)/11820000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((177851303:ℚ)/400000000),((-6870628338484515271632639154823333731451643668203951143:ℚ)/169172226660156250000000000000000000000000000000000000000),((-5519669589554516075963254597:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((872528317:ℚ)/1250000000),((7171564501:ℚ)/10000000000),((9372754853:ℚ)/15250000000),((8451564501:ℚ)/12010000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4066503931:ℚ)/10000000000),((-900875127051866088059959383197962723996526242961457717:ℚ)/22166113281250000000000000000000000000000000000000000000),((-5520544654885262222582388613:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((1774845799:ℚ)/2500000000),((7290713547:ℚ)/10000000000),((2716230313:ℚ)/4425000000),((8570713547:ℚ)/12200000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1824921463:ℚ)/5000000000),((-1834395348230110134001472430204115103375468001978259:ℚ)/45127221679687500000000000000000000000000000000000000),((-5521194166212134936235650117:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((3609263661:ℚ)/5000000000),((92623131:ℚ)/125000000),((38563372949:ℚ)/62900000000),((108623131:ℚ)/154875000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((636360833:ℚ)/2000000000),((-61723039477370266259571994247239397451420221596673661:ℚ)/1518909844970703125000000000000000000000000000000000000),((-862752843875057113878693:ℚ)/2310400000000000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((3668829743:ℚ)/5000000000),((7648090151:ℚ)/10000000000),((39099467687:ℚ)/64800000000),((8928090151:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1317553129:ℚ)/5000000000),((-257549603671686499827768689161911336133492415037699349:ℚ)/6998400000000000000000000000000000000000000000000000000),((-354215078496823:ℚ)/950000000000000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((7575890041:ℚ)/10000000000),((9552738289:ℚ)/10000000000),((80343010369:ℚ)/160000000000),((3610912763:ℚ)/4320000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((159349723:ℚ)/2000000000),((1419744334213724429194592894905691594596762356596708919:ℚ)/1600000000000000000000000000000000000000000000000000000000),((-5696889649544383:ℚ)/15200000000000000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((2370120237:ℚ)/2500000000),((13358186647:ℚ)/10000000000),((24371082133:ℚ)/55200000000),((14638186647:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((47901941825119876664217787:ℚ)/1523520000000000000000000000),((-383991239:ℚ)/1024000000)⟩
theorem valid11 : Valid source21 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC26
#check @N11Formalization.C450Source21GroupedC26.bound
#print axioms N11Formalization.C450Source21GroupedC26.valid0
#print axioms N11Formalization.C450Source21GroupedC26.valid1
#print axioms N11Formalization.C450Source21GroupedC26.valid2
#print axioms N11Formalization.C450Source21GroupedC26.valid3
#print axioms N11Formalization.C450Source21GroupedC26.valid4
#print axioms N11Formalization.C450Source21GroupedC26.valid5
#print axioms N11Formalization.C450Source21GroupedC26.valid6
#print axioms N11Formalization.C450Source21GroupedC26.valid7
#print axioms N11Formalization.C450Source21GroupedC26.valid8
#print axioms N11Formalization.C450Source21GroupedC26.valid9
#print axioms N11Formalization.C450Source21GroupedC26.valid10
#print axioms N11Formalization.C450Source21GroupedC26.valid11
#print axioms N11Formalization.C450Source21GroupedC26.bound
#print axioms N11Formalization.C450Source21GroupedC26.endpoint_checks
