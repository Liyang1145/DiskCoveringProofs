import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((31558411:ℚ)/50000000),((6634547911:ℚ)/10000000000),((-1834547911:ℚ)/24800000000),((4524767:ℚ)/496000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((236327773:ℚ)/400000000),((38944122640349274231727225105759369:ℚ)/762649600000000000000000000000000000),((-38433886452810616961:ℚ)/512000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((6553667413:ℚ)/10000000000),((3377689641:ℚ)/5000000000),((-977689641:ℚ)/12875000000),((178997761:ℚ)/103000000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5309534859:ℚ)/10000000000),((539514050751361078486506149313987883923075522594573:ℚ)/10421056747436523437500000000000000000000000000000000),((-656727325186704377474054569:ℚ)/7393280000000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((1668605401:ℚ)/2500000000),((272630649:ℚ)/400000000),((-80630649:ℚ)/1049000000),((-45816203:ℚ)/26462500000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((997365311:ℚ)/2000000000),((4616269622358612228428272592160247950672574695988037781:ℚ)/88584009505071250000000000000000000000000000000000000000),((-44249615060877538572088801:ℚ)/462080000000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((6734771049:ℚ)/10000000000),((687613471:ℚ)/1000000000),((-207613471:ℚ)/2646250000),((-364313147:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((4818176927:ℚ)/10000000000),((1006240002888219849096571977754856820232572749630342281:ℚ)/18980423404812011718750000000000000000000000000000000000),((-733739059910041050667078401:ℚ)/7393280000000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/4),((-3:ℚ)/16),((424693921:ℚ)/625000000),((6936485243:ℚ)/10000000000),((-2136485243:ℚ)/26700000000),((-34081763:ℚ)/6734375000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((928791039:ℚ)/2000000000),((714657421311446518305950651178922198495518356001325964161597:ℚ)/13259269323911250000000000000000000000000000000000000000000000),((-2967027767311628233992241:ℚ)/28880000000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((107115893:ℚ)/156250000),((6996818309:ℚ)/10000000000),((-2196818309:ℚ)/26937500000),((-11347679:ℚ)/1698437500),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4463503531:ℚ)/10000000000),((1581037675647440810799841646731832627511791789361539074025433:ℚ)/28869613102074890136718750000000000000000000000000000000000000),((-191761260547515255969449:ℚ)/1805000000000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((3457857381:ℚ)/5000000000),((7057134377:ℚ)/10000000000),((-2257134377:ℚ)/27175000000),((-453572143:ℚ)/54825000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2138013893:ℚ)/5000000000),((139776847606726412801698063170568637409545123617662024841207:ℚ)/2513359989801939697265625000000000000000000000000000000000000),((-202856058518941618280377161:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((3487998009:ℚ)/5000000000),((7117433899:ℚ)/10000000000),((-2317433899:ℚ)/27412500000),((-543994027:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2040277141:ℚ)/5000000000),((10336384511598555512463514389640641793705261210375767770149:ℚ)/183120832518288574218750000000000000000000000000000000000000),((-209367391959237101056722081:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((7036261353:ℚ)/10000000000),((904748129:ℚ)/1250000000),((-43535447:ℚ)/493750000),((-1268784059:ℚ)/112500000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1937933661:ℚ)/5000000000),((238270192692367880109520605936894364065921974094913:ℚ)/4062516174316406250000000000000000000000000000000000),((-863590245509383841834052609:ℚ)/7393280000000000000000000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((3578372961:ℚ)/5000000000),((1471695003:ℚ)/2000000000),((-170565001:ℚ)/1875000000),((-815118883:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3432166023:ℚ)/10000000000),((10144733361754851788628984817809921865640211930793279237:ℚ)/168494567871093750000000000000000000000000000000000000000),((-634389264544360389303561:ℚ)/5120000000000000000000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((7277171649:ℚ)/10000000000),((7599283661:ℚ)/10000000000),((-2799283661:ℚ)/28600000000),((-1991514947:ℚ)/118200000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2925118461:ℚ)/10000000000),((54786944595465008549672515123859442487508441361715732010179:ℚ)/851141620972500000000000000000000000000000000000000000000000),((-968828681908997564406297201:ℚ)/7393280000000000000000000000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((7517858233:ℚ)/10000000000),((391994107:ℚ)/500000000),((-151994107:ℚ)/1477500000),((-2713574699:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1471574181:ℚ)/10000000000),((3020698451593462120153732087533214619231090336327813873:ℚ)/45006309913535156250000000000000000000000000000000000000),((-1075281306443154734432784289:ℚ)/7393280000000000000000000000)⟩
theorem valid11 : Valid source32 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source32 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((7758342549:ℚ)/10000000000),((832052433:ℚ)/1000000000),((-352052433:ℚ)/3050000000),((-3435027647:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1446629299106741992602207913644076415553534866639364143:ℚ)/19390915898437500000000000000000000000000000000000000000),((-15400439:ℚ)/102400000)⟩
theorem valid12 : Valid source32 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((8238777197:ℚ)/10000000000),((10237663373:ℚ)/10000000000),((-5437663373:ℚ)/32400000000),((-4876331591:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((846374580563894879997262376117469720256193888491640803:ℚ)/7971615000000000000000000000000000000000000000000000000),((-15400439:ℚ)/102400000)⟩
theorem valid13 : Valid source32 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((10155288261:ℚ)/10000000000),((14057672533:ℚ)/10000000000),((-9257672533:ℚ)/40000000000),((-461994121:ℚ)/9600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1459271832764157011814081889458240089:ℚ)/9600000000000000000000000000000000000),((-15400439:ℚ)/102400000)⟩
theorem valid14 : Valid source32 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source32 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source32 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source32 nn0 nn1 Qcell ((2117:ℚ)/3200) ((2193:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source32 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source32 nn0 nn1 Qcell ((2193:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source32 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC13
#check @N11Formalization.C450Source32GroupedC13.bound
#print axioms N11Formalization.C450Source32GroupedC13.valid0
#print axioms N11Formalization.C450Source32GroupedC13.valid1
#print axioms N11Formalization.C450Source32GroupedC13.valid2
#print axioms N11Formalization.C450Source32GroupedC13.valid3
#print axioms N11Formalization.C450Source32GroupedC13.valid4
#print axioms N11Formalization.C450Source32GroupedC13.valid5
#print axioms N11Formalization.C450Source32GroupedC13.valid6
#print axioms N11Formalization.C450Source32GroupedC13.valid7
#print axioms N11Formalization.C450Source32GroupedC13.valid8
#print axioms N11Formalization.C450Source32GroupedC13.valid9
#print axioms N11Formalization.C450Source32GroupedC13.valid10
#print axioms N11Formalization.C450Source32GroupedC13.valid11
#print axioms N11Formalization.C450Source32GroupedC13.valid12
#print axioms N11Formalization.C450Source32GroupedC13.valid13
#print axioms N11Formalization.C450Source32GroupedC13.valid14
#print axioms N11Formalization.C450Source32GroupedC13.bound
#print axioms N11Formalization.C450Source32GroupedC13.endpoint_checks
