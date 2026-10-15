import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((6326011627:ℚ)/10000000000),((1650610901:ℚ)/2500000000),((-10114276307:ℚ)/24800000000),((-15778034881:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2937130427:ℚ)/5000000000),((2790122665291856257059682750096880395726195589079956531773:ℚ)/79393446093750000000000000000000000000000000000000000000000),((43103485945650816890408647:ℚ)/462080000000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((1640960923:ℚ)/2500000000),((3420150973:ℚ)/5000000000),((-21061056811:ℚ)/51500000000),((-4122882769:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5283031473:ℚ)/10000000000),((13397169862981736324954825511464933419890048049766449927:ℚ)/382913825976562500000000000000000000000000000000000000000),((170311974478571066425302263:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((6801652081:ℚ)/10000000000),((3479610851:ℚ)/5000000000),((-21477275957:ℚ)/53400000000),((-17204956243:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((578084677:ℚ)/1250000000),((9145924769846907945242418102779114283676861352215591325569:ℚ)/267910616641406250000000000000000000000000000000000000000000),((168062105873762378148891447:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((276821927:ℚ)/400000000),((7018679369:ℚ)/10000000000),((-43370755583:ℚ)/108700000000),((-702465781:ℚ)/2193000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2130332873:ℚ)/5000000000),((201456269037697674981638915701437631011166850667784009:ℚ)/5970960668207812500000000000000000000000000000000000000),((667753040314504221493147567:ℚ)/7393280000000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((6979994319:ℚ)/10000000000),((1769533903:ℚ)/2500000000),((-10946737321:ℚ)/27412500000),((-17739982957:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1016819089:ℚ)/2500000000),((407108626377801370212297838347883681342943614568523908727:ℚ)/12072377694042968750000000000000000000000000000000000000000),((41604144636198535242456223:ℚ)/462080000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((175985981:ℚ)/250000000),((713759047:ℚ)/1000000000),((-4420313329:ℚ)/11060000000),((-447957943:ℚ)/1394375000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1932394497:ℚ)/5000000000),((19739190754315215345120486265438708193928111402162439:ℚ)/585630826208400726318359375000000000000000000000000000),((6635823216919676652591823:ℚ)/73932800000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-7:ℚ)/16),((-3:ℚ)/8),((7098882967:ℚ)/10000000000),((716731739:ℚ)/1000000000),((-4441122173:ℚ)/11155000000),((-18096648901:ℚ)/56012500000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((730337301:ℚ)/2000000000),((3285300740548406657294312140662170825403233979881092400579:ℚ)/98015430042026855468750000000000000000000000000000000000000),((6613384956329400695707687:ℚ)/73932800000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((7128604393:ℚ)/10000000000),((899630497:ℚ)/1250000000),((-5577413479:ℚ)/14003125000),((-18185813179:ℚ)/56250000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((35405581:ℚ)/100000000),((1957482696298830035566294874921083672102280289211620013337:ℚ)/58412235975265502929687500000000000000000000000000000000000),((10317159669475358429875423:ℚ)/115520000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-7:ℚ)/16),((-3:ℚ)/8),((1789581383:ℚ)/2500000000),((7226770233:ℚ)/10000000000),((-14942463877:ℚ)/37500000000),((-4568744149:ℚ)/14121875000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((3425984379:ℚ)/10000000000),((1769242523863464114204049314386871835383871418284774943:ℚ)/52805402961158752441406250000000000000000000000000000000),((1977775874145026997095312749:ℚ)/22179840000000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((7188046387:ℚ)/10000000000),((1814124041:ℚ)/2500000000),((-11258868287:ℚ)/28243750000),((-18364139161:ℚ)/56725000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((3307606789:ℚ)/10000000000),((431729044015442413985827329456342976155022453037408368351:ℚ)/12888010493547607421875000000000000000000000000000000000000),((41138732069470144181209007:ℚ)/462080000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-7:ℚ)/16),((-3:ℚ)/8),((7217766963:ℚ)/10000000000),((291448871:ℚ)/400000000),((-1809742097:ℚ)/4538000000),((-18453300889:ℚ)/56962500000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((1592500329:ℚ)/5000000000),((29261972457880879553064012573846187471973554461292903485823:ℚ)/873696072169665527343750000000000000000000000000000000000000),((1051490374151618297962127:ℚ)/11829248000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((7247487263:ℚ)/10000000000),((7315947069:ℚ)/10000000000),((-15150543161:ℚ)/37975000000),((-18542461789:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((1528828391:ℚ)/5000000000),((59496080143779194429533542445173024215808980918843639293211:ℚ)/1776748173200000000000000000000000000000000000000000000000000),((1968431810364893547015459301:ℚ)/22179840000000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((7277207289:ℚ)/10000000000),((92192459:ℚ)/125000000),((-573347213:ℚ)/1430000000),((-18631621867:ℚ)/57675000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((292495583:ℚ)/1000000000),((61459801454491788575975371075274500448242757002242973:ℚ)/1826701008899688720703125000000000000000000000000000000),((102386510020904858793007:ℚ)/1155200000000000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((3668323269:ℚ)/5000000000),((148696903:ℚ)/200000000),((-925678321:ℚ)/2307000000),((-9404969807:ℚ)/29075000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((660054597:ℚ)/2500000000),((11918753423250140322351405978368449165305094967548287068029:ℚ)/354394343977441406250000000000000000000000000000000000000000),((261281328792447278742223:ℚ)/2957312000000000000000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((1479216947:ℚ)/2000000000),((3776869231:ℚ)/5000000000),((-23558084617:ℚ)/58150000000),((-3797650841:ℚ)/11820000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2321715111:ℚ)/10000000000),((3772007498766062961768123177889899643337702641392483569:ℚ)/111144609987500000000000000000000000000000000000000000000),((162869068149219970107727967:ℚ)/1848320000000000000000000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/16),((-3:ℚ)/8),((7514958077:ℚ)/10000000000),((7791511671:ℚ)/10000000000),((-16260193899:ℚ)/39400000000),((-19344874231:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((748687437:ℚ)/5000000000),((28941088942370835840069694129211357902199374351128507773921:ℚ)/838411068750000000000000000000000000000000000000000000000000),((42561335216538651:ℚ)/486400000000000000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((3876346609:ℚ)/5000000000),((8267009951:ℚ)/10000000000),((-52109069657:ℚ)/122000000000),((-10029039827:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((153743901800444199742352029819667315395119587664667581101:ℚ)/4322386800000000000000000000000000000000000000000000000000),((44563061:ℚ)/512000000)⟩
theorem valid16 : Valid source11 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((8228122077:ℚ)/10000000000),((10168529159:ℚ)/10000000000),((-65419704113:ℚ)/129600000000),((-21484366231:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((10619589400379791372916143132836072485380705580776950601031:ℚ)/259200000000000000000000000000000000000000000000000000000000),((44563061:ℚ)/512000000)⟩
theorem valid17 : Valid source11 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((158272339:ℚ)/156250000),((6985155853:ℚ)/5000000000),((-46016090971:ℚ)/80000000000),((-424817017:ℚ)/1725000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1126013546495204606752620265068706934333157036605299:ℚ)/24060717773437500000000000000000000000000000000000000),((44563061:ℚ)/512000000)⟩
theorem valid18 : Valid source11 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source11 nn0 nn1 Qcell ((4481:ℚ)/6400) ((4519:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((4519:ℚ)/6400) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source11 nn0 nn1 Qcell ((4519:ℚ)/6400) ((4557:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source11 nn0 nn1 Qcell ((4557:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source11 nn0 nn1 Qcell ((4519:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source11 nn0 nn1 Qcell ((4519:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC10
#check @N11Formalization.C450Source11GroupedC10.bound
#print axioms N11Formalization.C450Source11GroupedC10.valid0
#print axioms N11Formalization.C450Source11GroupedC10.valid1
#print axioms N11Formalization.C450Source11GroupedC10.valid2
#print axioms N11Formalization.C450Source11GroupedC10.valid3
#print axioms N11Formalization.C450Source11GroupedC10.valid4
#print axioms N11Formalization.C450Source11GroupedC10.valid5
#print axioms N11Formalization.C450Source11GroupedC10.valid6
#print axioms N11Formalization.C450Source11GroupedC10.valid7
#print axioms N11Formalization.C450Source11GroupedC10.valid8
#print axioms N11Formalization.C450Source11GroupedC10.valid9
#print axioms N11Formalization.C450Source11GroupedC10.valid10
#print axioms N11Formalization.C450Source11GroupedC10.valid11
#print axioms N11Formalization.C450Source11GroupedC10.valid12
#print axioms N11Formalization.C450Source11GroupedC10.valid13
#print axioms N11Formalization.C450Source11GroupedC10.valid14
#print axioms N11Formalization.C450Source11GroupedC10.valid15
#print axioms N11Formalization.C450Source11GroupedC10.valid16
#print axioms N11Formalization.C450Source11GroupedC10.valid17
#print axioms N11Formalization.C450Source11GroupedC10.valid18
#print axioms N11Formalization.C450Source11GroupedC10.bound
#print axioms N11Formalization.C450Source11GroupedC10.endpoint_checks
