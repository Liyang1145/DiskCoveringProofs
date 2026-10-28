import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((3355913013:ℚ)/5000000000),((6915831747:ℚ)/10000000000),((-61994149217:ℚ)/99200000000),((-2619913013:ℚ)/5055000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4882928461:ℚ)/10000000000),((710694465817658804117819502055766700355838864278576576160997893:ℚ)/3118080687206400000000000000000000000000000000000000000000000000),((166330491115687140196233419:ℚ)/443596800000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((6831297759:ℚ)/10000000000),((3517619337:ℚ)/5000000000),((-31653812707:ℚ)/50550000000),((-5359297759:ℚ)/10300000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((1134116531:ℚ)/2500000000),((2929575200497808708033267907246463221327505364066899415798869:ℚ)/12847221313569140625000000000000000000000000000000000000000000),((662055326658435189707239331:ℚ)/1774387200000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((695074263:ℚ)/1000000000),((7094933059:ℚ)/10000000000),((-63964263649:ℚ)/103000000000),((-547874263:ℚ)/1039500000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((1040873651:ℚ)/2500000000),((824958208433375635913262654958296818138767877955906338455692461:ℚ)/3689866750942968750000000000000000000000000000000000000000000000),((6587419728525986146038419:ℚ)/17743872000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7010455459:ℚ)/10000000000),((1424955611:ℚ)/2000000000),((-1168955611:ℚ)/1890000000),((-5538455459:ℚ)/10442500000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((31717921:ℚ)/80000000),((2910694037985707953770539372369619257744831707699864534793:ℚ)/13146385202064843750000000000000000000000000000000000000000),((219022591439875396539855977:ℚ)/591462400000000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((1760077387:ℚ)/2500000000),((3577310807:ℚ)/5000000000),((-32310418877:ℚ)/52212500000),((-1392077387:ℚ)/2622500000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((1930874889:ℚ)/5000000000),((27099968075088584839543909385587517864539480615574285764326673:ℚ)/122367044725168507385253906250000000000000000000000000000000000),((13671381128445444947947673:ℚ)/36966400000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-11:ℚ)/16),((-5:ℚ)/8),((7070162117:ℚ)/10000000000),((3592231877:ℚ)/5000000000),((-32474550647:ℚ)/52450000000),((-1866054039:ℚ)/3512500000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((751217457:ℚ)/2000000000),((78870559681401837156221179128634793115729256228164135492267:ℚ)/356040284240972656250000000000000000000000000000000000000000),((218460631058488873708512313:ℚ)/591462400000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((1420002637:ℚ)/2000000000),((450894031:ℚ)/625000000),((-4079834341:ℚ)/6585937500),((-1125602637:ℚ)/2117000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((3647519853:ℚ)/10000000000),((295493529930435135312569606134764126273099076266457089554317:ℚ)/1333592971460880339145660400390625000000000000000000000000000),((8727127616830890360649673:ℚ)/23658496000000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7129862773:ℚ)/10000000000),((3622071929:ℚ)/5000000000),((-32802791219:ℚ)/52925000000),((-5657862773:ℚ)/10632500000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((1767889649:ℚ)/5000000000),((1857181823898409577315588543076004296941183001073071531500180279:ℚ)/8379601911990454931640625000000000000000000000000000000000000000),((217894776091243901248301593:ℚ)/591462400000000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((7159710901:ℚ)/10000000000),((7273981859:ℚ)/10000000000),((-65933800449:ℚ)/106325000000),((-5687710901:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((684110809:ℚ)/2000000000),((14840674283732769974835420308769992388103906977323466804668189:ℚ)/66945089612122229003906250000000000000000000000000000000000000),((217610388025928039342373017:ℚ)/591462400000000000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((1797389397:ℚ)/2500000000),((7303818517:ℚ)/10000000000),((-66262003687:ℚ)/106800000000),((-1429389397:ℚ)/2681875000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((103171207:ℚ)/312500000),((242849471831643000736204274948058055352359260313364696329885147:ℚ)/1095218660690634375000000000000000000000000000000000000000000000),((40748442410207304800158859:ℚ)/110899200000000000000000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-11:ℚ)/16),((-5:ℚ)/8),((1443880571:ℚ)/2000000000),((146673077:ℚ)/200000000),((-1331803847:ℚ)/2145500000),((-1149480571:ℚ)/2155000000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1589059821:ℚ)/5000000000),((2128671837567447235389712061641208915278581626457143963:ℚ)/9597836954968565368652343750000000000000000000000000000),((8681547620719270187271097:ℚ)/23658496000000000000000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((7249246719:ℚ)/10000000000),((1848330153:ℚ)/2500000000),((-16811631683:ℚ)/26937500000),((-5777246719:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3049956713:ℚ)/10000000000),((16166591539624935132752191599099979975665688038094898125880047:ℚ)/72174032755187225341796875000000000000000000000000000000000000),((1801258013796816540255851:ℚ)/4915200000000000000000000)⟩
theorem valid11 : Valid source24 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source24 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7308930317:ℚ)/10000000000),((7452982281:ℚ)/10000000000),((-67902805091:ℚ)/108700000000),((-1945643439:ℚ)/3655000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2776531461:ℚ)/10000000000),((120140358666615963563140826291629844731953179370679464191559239:ℚ)/536183464491080468750000000000000000000000000000000000000000000),((598819501857760238200033:ℚ)/1638400000000000000000000)⟩
theorem valid12 : Valid source24 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((3684304263:ℚ)/5000000000),((7512638991:ℚ)/10000000000),((-4032884053:ℚ)/6450000000),((-2948304263:ℚ)/5530000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((494788917:ℚ)/2000000000),((34103534108979451132928116406583416078265035378428188781:ℚ)/152157588848876953125000000000000000000000000000000000000),((161694302557137934237218419:ℚ)/443596800000000000000000000)⟩
theorem valid13 : Valid source24 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source24 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-11:ℚ)/16),((-5:ℚ)/8),((7428281487:ℚ)/10000000000),((3815969019:ℚ)/5000000000),((-34935659209:ℚ)/55300000000),((-5956281487:ℚ)/11250000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((425959089:ℚ)/2000000000),((5454711612137999978330593008743985562002011717126832683:ℚ)/23887595104980468750000000000000000000000000000000000000),((645021211175738147777676419:ℚ)/1774387200000000000000000000)⟩
theorem valid14 : Valid source24 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source24 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((3773806101:ℚ)/5000000000),((310048749:ℚ)/400000000),((-2847336239:ℚ)/4500000000),((-276164191:ℚ)/520000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((29370617:ℚ)/250000000),((10990749672099336408516441316413582784051580337019091939:ℚ)/48125390625000000000000000000000000000000000000000000000),((160368535797500168958109451:ℚ)/443596800000000000000000000)⟩
theorem valid15 : Valid source24 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((766692349:ℚ)/1000000000),((87049009:ℚ)/100000000),((-74249009:ℚ)/104000000),((-619492349:ℚ)/1296000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((166731854704300026250977940220755568511308675879099:ℚ)/591364800000000000000000000000000000000000000000000),((369287843:ℚ)/1024000000)⟩
theorem valid16 : Valid source24 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((43104089:ℚ)/50000000),((331567433:ℚ)/312500000),((-3207241763:ℚ)/4050000000),((-35744089:ℚ)/80000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((203582183732439097551199798597107868601315014918773749:ℚ)/622782421875000000000000000000000000000000000000000000),((369287843:ℚ)/1024000000)⟩
theorem valid17 : Valid source24 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((2105275419:ℚ)/2000000000),((14416318641:ℚ)/10000000000),((-144499505051:ℚ)/160000000000),((-1810875419:ℚ)/4416000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((994878344846376495617833385254194734202397:ℚ)/2437632000000000000000000000000000000000000),((369287843:ℚ)/1024000000)⟩
theorem valid18 : Valid source24 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((4177:ℚ)/6400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((4177:ℚ)/6400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source24 nn0 nn1 Qcell ((4177:ℚ)/6400) ((843:ℚ)/1280) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source24 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source24 nn0 nn1 Qcell ((843:ℚ)/1280) ((267:ℚ)/400) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source24 nn0 nn1 Qcell ((4177:ℚ)/6400) ((267:ℚ)/400) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source24 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC06
#check @N11Formalization.C450Source24GroupedC06.bound
#print axioms N11Formalization.C450Source24GroupedC06.valid0
#print axioms N11Formalization.C450Source24GroupedC06.valid1
#print axioms N11Formalization.C450Source24GroupedC06.valid2
#print axioms N11Formalization.C450Source24GroupedC06.valid3
#print axioms N11Formalization.C450Source24GroupedC06.valid4
#print axioms N11Formalization.C450Source24GroupedC06.valid5
#print axioms N11Formalization.C450Source24GroupedC06.valid6
#print axioms N11Formalization.C450Source24GroupedC06.valid7
#print axioms N11Formalization.C450Source24GroupedC06.valid8
#print axioms N11Formalization.C450Source24GroupedC06.valid9
#print axioms N11Formalization.C450Source24GroupedC06.valid10
#print axioms N11Formalization.C450Source24GroupedC06.valid11
#print axioms N11Formalization.C450Source24GroupedC06.valid12
#print axioms N11Formalization.C450Source24GroupedC06.valid13
#print axioms N11Formalization.C450Source24GroupedC06.valid14
#print axioms N11Formalization.C450Source24GroupedC06.valid15
#print axioms N11Formalization.C450Source24GroupedC06.valid16
#print axioms N11Formalization.C450Source24GroupedC06.valid17
#print axioms N11Formalization.C450Source24GroupedC06.valid18
#print axioms N11Formalization.C450Source24GroupedC06.bound
#print axioms N11Formalization.C450Source24GroupedC06.endpoint_checks
