import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((6517621861:ℚ)/10000000000),((1704521079:ℚ)/2500000000),((-1464521079:ℚ)/2480000000),((-48418596749:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((675308361:ℚ)/1250000000),((32515116852288493010869162901028194216234079789311625383:ℚ)/505684350400000000000000000000000000000000000000000000000),((98046886925189068673060733:ℚ)/369664000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((6755857459:ℚ)/10000000000),((6937187017:ℚ)/10000000000),((-5977187017:ℚ)/10300000000),((-50562717131:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4757955319:ℚ)/10000000000),((58086907844434065064673471503881846405768470119487595438481:ℚ)/939404596505468750000000000000000000000000000000000000000000),((97457493072850528291424013:ℚ)/369664000000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((429684699:ℚ)/625000000),((6996733599:ℚ)/10000000000),((-6036733599:ℚ)/10490000000),((-3227162291:ℚ)/6615625000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4403574199:ℚ)/10000000000),((463335911007852033205276258040855737186927201319249206939:ℚ)/7636552543540625000000000000000000000000000000000000000000),((1138601684307556534798519:ℚ)/4332000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((1386899869:ℚ)/2000000000),((1411255423:ℚ)/2000000000),((-1219255423:ℚ)/2117000000),((-10434098821:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((2108015039:ℚ)/5000000000),((48831404439534346893437388184272098084528828150554007:ℚ)/804284608203906250000000000000000000000000000000000000),((3880469548113666429403053:ℚ)/14786560000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/8),((-9:ℚ)/16),((1748510121:ℚ)/2500000000),((7115817647:ℚ)/10000000000),((-6155817647:ℚ)/10680000000),((-13176591089:ℚ)/26937500000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2010151187:ℚ)/5000000000),((503459824963562211154221462857404156924884346955085822557:ℚ)/8287043327444531250000000000000000000000000000000000000000),((18161708732022998892649279:ℚ)/69312000000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((3526789341:ℚ)/5000000000),((7145586819:ℚ)/10000000000),((-6185586819:ℚ)/10775000000),((-26621104069:ℚ)/54112500000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((95378191:ℚ)/250000000),((275647638917999125055507136191075245522272501981965148746483:ℚ)/4578856648317965698242187500000000000000000000000000000000000),((72534600386952273169506439:ℚ)/277248000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((3541673351:ℚ)/5000000000),((287014211:ℚ)/400000000),((-6719303:ℚ)/11700000),((-26755060159:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1854254593:ℚ)/5000000000),((118712288885458389265385023274470868268187384081333:ℚ)/1971266948746875000000000000000000000000000000000000),((24159461181009359518993973:ℚ)/92416000000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((1422622803:ℚ)/2000000000),((3602561511:ℚ)/5000000000),((-3122561511:ℚ)/5435000000),((-10755605227:ℚ)/21835000000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((359888619:ℚ)/1000000000),((3274928405769035822045136396914288214599836517751402140157:ℚ)/54362870805312426757812500000000000000000000000000000000000),((11587536048013032361863271:ℚ)/44359680000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7142880631:ℚ)/10000000000),((904361259:ℚ)/1250000000),((-71305569:ℚ)/124062500),((-54045925679:ℚ)/109650000000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((1742987331:ℚ)/5000000000),((40218445423183226356531048140277846382369406828972949:ℚ)/667391106094264984130859375000000000000000000000000000),((96487667525328950693796053:ℚ)/369664000000000000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-5:ℚ)/8),((-9:ℚ)/16),((7172646559:ℚ)/10000000000),((7264656433:ℚ)/10000000000),((-6304656433:ℚ)/10965000000),((-54313819031:ℚ)/110125000000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((26323777:ℚ)/78125000),((48189716683665356705248676588578324004347228698080883887929:ℚ)/799406647285564160156250000000000000000000000000000000000000),((96412446083284685172241413:ℚ)/369664000000000000000000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((225075369:ℚ)/312500000),((3647211057:ℚ)/5000000000),((-3167211057:ℚ)/5506250000),((-1705678321:ℚ)/3456250000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1624451261:ℚ)/5000000000),((150318640218039373674921641870624961283850522342500659569:ℚ)/2492803740005123615264892578125000000000000000000000000000),((282237703293318307720159:ℚ)/1083000000000000000000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((3616088193:ℚ)/5000000000),((735395147:ℚ)/1000000000),((-639395147:ℚ)/1106000000),((-27424793737:ℚ)/55775000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3123887133:ℚ)/10000000000),((11439958965215761347779462622896172730963114034803083453:ℚ)/187886908459173437500000000000000000000000000000000000000),((72196303075301259523527631:ℚ)/277248000000000000000000000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/8),((-9:ℚ)/16),((3645851783:ℚ)/5000000000),((741347821:ℚ)/1000000000),((-645347821:ℚ)/1115500000),((-27692666047:ℚ)/56250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2858061717:ℚ)/10000000000),((861922148837358978243775918346989798077637268639:ℚ)/14149205845642089843750000000000000000000000000000),((24027668580765450536198197:ℚ)/92416000000000000000000000)⟩
theorem valid12 : Valid source17 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source17 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source17 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((1470245633:ℚ)/2000000000),((75325241:ℚ)/100000000),((-65725241:ℚ)/112500000),((-1016746427:ℚ)/2080000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((513133807:ℚ)/2000000000),((46655995573508092408806512640958703504805588959327:ℚ)/751959228515625000000000000000000000000000000000000),((3838370265254143319164997:ℚ)/14786560000000000000000000)⟩
theorem valid13 : Valid source17 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((1867567471:ℚ)/2500000000),((3885293621:ℚ)/5000000000),((-3405293621:ℚ)/5720000000),((-14248107239:ℚ)/29550000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((370065261:ℚ)/2000000000),((1092849750270048296475523288807435421658369572163144347911:ℚ)/17022832419450000000000000000000000000000000000000000000000),((5978459813572993086430693:ℚ)/23104000000000000000000000)⟩
theorem valid14 : Valid source17 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/8),((-9:ℚ)/16),((7708325087:ℚ)/10000000000),((1601723037:ℚ)/2000000000),((-469907679:ℚ)/788000000),((-59134925783:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((364948295657224007274939609116816452167159508723637967:ℚ)/5689686586600000000000000000000000000000000000000000000),((6601283:ℚ)/25600000)⟩
theorem valid15 : Valid source17 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((794634559:ℚ)/1000000000),((4242288957:ℚ)/5000000000),((-3762288957:ℚ)/6100000000),((-6127711031:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((316025568125434234629888800304721321823946123875474557549:ℚ)/4653819815625000000000000000000000000000000000000000000000),((6601283:ℚ)/25600000)⟩
theorem valid16 : Valid source17 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((4211147377:ℚ)/5000000000),((2077502441:ℚ)/2000000000),((-1885502441:ℚ)/2592000000),((-32780326393:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((14381431392632599982541981628257644987324762370889739:ℚ)/163258675200000000000000000000000000000000000000000000),((6601283:ℚ)/25600000)⟩
theorem valid17 : Valid source17 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((1032518773:ℚ)/1000000000),((14190953559:ℚ)/10000000000),((-13230953559:ℚ)/16000000000),((-8268668957:ℚ)/22080000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1668290972271455409586983618139802877567076630714981839767:ℚ)/15235200000000000000000000000000000000000000000000000000000),((6601283:ℚ)/25600000)⟩
theorem valid18 : Valid source17 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source17 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((4329:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source17 nn0 nn1 Qcell ((4329:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source17 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source17 nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source17 nn0 nn1 Qcell ((2193:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source17 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC07
#check @N11Formalization.C450Source17GroupedC07.bound
#print axioms N11Formalization.C450Source17GroupedC07.valid0
#print axioms N11Formalization.C450Source17GroupedC07.valid1
#print axioms N11Formalization.C450Source17GroupedC07.valid2
#print axioms N11Formalization.C450Source17GroupedC07.valid3
#print axioms N11Formalization.C450Source17GroupedC07.valid4
#print axioms N11Formalization.C450Source17GroupedC07.valid5
#print axioms N11Formalization.C450Source17GroupedC07.valid6
#print axioms N11Formalization.C450Source17GroupedC07.valid7
#print axioms N11Formalization.C450Source17GroupedC07.valid8
#print axioms N11Formalization.C450Source17GroupedC07.valid9
#print axioms N11Formalization.C450Source17GroupedC07.valid10
#print axioms N11Formalization.C450Source17GroupedC07.valid11
#print axioms N11Formalization.C450Source17GroupedC07.valid12
#print axioms N11Formalization.C450Source17GroupedC07.valid13
#print axioms N11Formalization.C450Source17GroupedC07.valid14
#print axioms N11Formalization.C450Source17GroupedC07.valid15
#print axioms N11Formalization.C450Source17GroupedC07.valid16
#print axioms N11Formalization.C450Source17GroupedC07.valid17
#print axioms N11Formalization.C450Source17GroupedC07.valid18
#print axioms N11Formalization.C450Source17GroupedC07.bound
#print axioms N11Formalization.C450Source17GroupedC07.endpoint_checks
