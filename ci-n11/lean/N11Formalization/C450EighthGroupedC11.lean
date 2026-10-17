import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((6270807047:ℚ)/10000000000),((204289527:ℚ)/312500000),((-552868581:ℚ)/1550000000),((-5374807047:ℚ)/20600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6004061979:ℚ)/10000000000),((26514147913710033240409224472681275771611181695328105431:ℚ)/1693726850000000000000000000000000000000000000000000000000),((109164917811726091539239:ℚ)/1805000000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((3254230919:ℚ)/5000000000),((6774951277:ℚ)/10000000000),((-18404853831:ℚ)/51500000000),((-2806230919:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((339115889:ℚ)/625000000),((3052870192711896302951983326949875883794695921361941519:ℚ)/196051878900000000000000000000000000000000000000000000000),((5829361718813134026023881:ℚ)/97280000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((6746105603:ℚ)/10000000000),((689378959:ℚ)/1000000000),((-625378959:ℚ)/1780000000),((-5850105603:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2392946477:ℚ)/5000000000),((87027860997472034455934345825756991476376016991362227141:ℚ)/5715426488350000000000000000000000000000000000000000000000),((1096066839690240041743571:ℚ)/18483200000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((6864923713:ℚ)/10000000000),((3476603799:ℚ)/5000000000),((-9469811397:ℚ)/27175000000),((-5968923713:ℚ)/21930000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((1108609587:ℚ)/2500000000),((89956451110787353195214339486267058054031475235693367891:ℚ)/5970960668207812500000000000000000000000000000000000000000),((27257990840779545663669091:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((3462165941:ℚ)/5000000000),((3506312433:ℚ)/5000000000),((-3186312433:ℚ)/9137500000),((-3014165941:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4248603609:ℚ)/10000000000),((4362005750582911946507612222493496776084099948092109379:ℚ)/289737064657031250000000000000000000000000000000000000000),((27194592866480126131346899:ℚ)/462080000000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((6983739481:ℚ)/10000000000),((7072041413:ℚ)/10000000000),((-2756589177:ℚ)/7900000000),((-6087739481:ℚ)/22310000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((810960369:ℚ)/2000000000),((5155518089776674586376469146858577412936176891077859297:ℚ)/342677694878515625000000000000000000000000000000000000000),((108525351566316270767789179:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((1760786631:ℚ)/2500000000),((3565728629:ℚ)/5000000000),((-9737185887:ℚ)/27887500000),((-1536786631:ℚ)/5625000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((962956729:ℚ)/2500000000),((437249402408615187951699113095170782646281325710477341:ℚ)/29082280397415161132812500000000000000000000000000000000),((27068225897472927293051931:ℚ)/462080000000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-3:ℚ)/8),((-5:ℚ)/16),((3551276513:ℚ)/5000000000),((7161164923:ℚ)/10000000000),((-2173721641:ℚ)/6250000000),((-3103276513:ℚ)/11297500000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((3638139867:ℚ)/10000000000),((134827080746130902615883324222277853025315445924236871:ℚ)/9012122105371093750000000000000000000000000000000000000),((5683506515376576607426681:ℚ)/97280000000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((3566128039:ℚ)/5000000000),((3595436209:ℚ)/5000000000),((-9826308627:ℚ)/28243750000),((-3118128039:ℚ)/11345000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((1763336703:ℚ)/5000000000),((1542066558187839515392185975016420342885609519454716703:ℚ)/103104083948380859375000000000000000000000000000000000000),((26965189478352093444031571:ℚ)/462080000000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-3:ℚ)/8),((-5:ℚ)/16),((7161958999:ℚ)/10000000000),((7220579747:ℚ)/10000000000),((-19741739241:ℚ)/56725000000),((-6265958999:ℚ)/22785000000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((3411724339:ℚ)/10000000000),((836078433691942912380562188715028201520421788175974057551:ℚ)/55916548618858593750000000000000000000000000000000000000000),((5670264998598529402645801:ℚ)/97280000000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((224739431:ℚ)/312500000),((7250286911:ℚ)/10000000000),((-6610286911:ℚ)/18987500000),((-196739431:ℚ)/715000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((1646463719:ℚ)/5000000000),((51873337829121049631886939434432044293372782669536663:ℚ)/3470211275781250000000000000000000000000000000000000000),((107609454954641371137727411:ℚ)/1848320000000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((-3:ℚ)/8),((-5:ℚ)/16),((3610682229:ℚ)/5000000000),((909999239:ℚ)/1250000000),((-2489997717:ℚ)/7150000000),((-3162682229:ℚ)/11487500000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((3169849569:ℚ)/10000000000),((60741561052261077506530600056317577233081522631789757583:ℚ)/4064563217907714843750000000000000000000000000000000000000),((1679437778934330859852611:ℚ)/28880000000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((3625533499:ℚ)/5000000000),((456856297:ℚ)/625000000),((-1250568891:ℚ)/3589843750),((-1059177833:ℚ)/3845000000),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((760492647:ℚ)/2500000000),((571641640566360490648448866423047309365001120529147:ℚ)/38261839935699462890625000000000000000000000000000000),((419370014294760548796419:ℚ)/7220000000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((3640384707:ℚ)/5000000000),((3684556979:ℚ)/5000000000),((-3364556979:ℚ)/9612500000),((-3192384707:ℚ)/11630000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2908656727:ℚ)/10000000000),((113396269653006876524554038825429081824968422669145275221:ℚ)/7560412671518750000000000000000000000000000000000000000000),((26817207354112590961330731:ℚ)/462080000000000000000000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-3:ℚ)/8),((-5:ℚ)/16),((7340173881:ℚ)/10000000000),((1485705309:ℚ)/2000000000),((-4073115927:ℚ)/11630000000),((-6444173881:ℚ)/23450000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((131118729:ℚ)/500000000),((4215253213591023528487104557144061986423145930801576280087:ℚ)/281196252110156250000000000000000000000000000000000000000000),((4280769598306423335247371:ℚ)/73932800000000000000000000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((739957787:ℚ)/1000000000),((7487938527:ℚ)/10000000000),((-20543815581:ℚ)/58625000000),((-216785929:ℚ)/788000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1150827157:ℚ)/5000000000),((5372237670511887500218826446601397068571039697873787:ℚ)/358567993700000000000000000000000000000000000000000000),((106770222002074140850762739:ℚ)/1848320000000000000000000000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((7458981393:ℚ)/10000000000),((7606760733:ℚ)/10000000000),((-6966760733:ℚ)/19700000000),((-6562981393:ℚ)/24020000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((24117387:ℚ)/125000000),((193162775810210837077449582274196833058482153112666510929:ℚ)/12797540602387500000000000000000000000000000000000000000000),((3506122608575037:ℚ)/60800000000000000)⟩
theorem valid16 : Valid eighth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((1894446771:ℚ)/2500000000),((7725580689:ℚ)/10000000000),((-21256742067:ℚ)/60050000000),((-1670446771:ℚ)/6100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((152949063:ℚ)/2000000000),((77060866975522236462757187650902028089012120000047950391:ℚ)/5111328393750000000000000000000000000000000000000000000000),((871258916918439:ℚ)/15200000000000000)⟩
theorem valid17 : Valid eighth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((7696591039:ℚ)/10000000000),((512552499:ℚ)/625000000),((-1417657497:ℚ)/3812500000),((-6800591039:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((34778049986512866499082325853395182346158418867537514471:ℚ)/2213062041600000000000000000000000000000000000000000000000),((7328617:ℚ)/128000000)⟩
theorem valid18 : Valid eighth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((8171791029:ℚ)/10000000000),((2020326137:ℚ)/2000000000),((-630775379:ℚ)/1440000000),((-7275791029:ℚ)/32000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((10899708642469088713647522596738970725782051601967887689:ℚ)/614400000000000000000000000000000000000000000000000000000),((7328617:ℚ)/128000000)⟩
theorem valid19 : Valid eighth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((1007240091:ℚ)/1000000000),((13902558663:ℚ)/10000000000),((-39787675989:ℚ)/80000000000),((-917640091:ℚ)/4416000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((8110752775796067659926395686652316578619560567371951:ℚ)/403671859200000000000000000000000000000000000000000000),((7328617:ℚ)/128000000)⟩
theorem valid20 : Valid eighth packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound eighth nn0 nn1 Qcell ((4519:ℚ)/6400) ((4557:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((4557:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((4557:ℚ)/6400) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((4557:ℚ)/6400) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound eighth nn0 nn1 Qcell ((4557:ℚ)/6400) ((919:ℚ)/1280) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound eighth nn0 nn1 Qcell ((919:ℚ)/1280) ((469:ℚ)/640) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound eighth nn0 nn1 Qcell ((4557:ℚ)/6400) ((469:ℚ)/640) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound eighth nn0 nn1 Qcell ((4557:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC11
#check @N11Formalization.C450EighthGroupedC11.bound
#print axioms N11Formalization.C450EighthGroupedC11.valid0
#print axioms N11Formalization.C450EighthGroupedC11.valid1
#print axioms N11Formalization.C450EighthGroupedC11.valid2
#print axioms N11Formalization.C450EighthGroupedC11.valid3
#print axioms N11Formalization.C450EighthGroupedC11.valid4
#print axioms N11Formalization.C450EighthGroupedC11.valid5
#print axioms N11Formalization.C450EighthGroupedC11.valid6
#print axioms N11Formalization.C450EighthGroupedC11.valid7
#print axioms N11Formalization.C450EighthGroupedC11.valid8
#print axioms N11Formalization.C450EighthGroupedC11.valid9
#print axioms N11Formalization.C450EighthGroupedC11.valid10
#print axioms N11Formalization.C450EighthGroupedC11.valid11
#print axioms N11Formalization.C450EighthGroupedC11.valid12
#print axioms N11Formalization.C450EighthGroupedC11.valid13
#print axioms N11Formalization.C450EighthGroupedC11.valid14
#print axioms N11Formalization.C450EighthGroupedC11.valid15
#print axioms N11Formalization.C450EighthGroupedC11.valid16
#print axioms N11Formalization.C450EighthGroupedC11.valid17
#print axioms N11Formalization.C450EighthGroupedC11.valid18
#print axioms N11Formalization.C450EighthGroupedC11.valid19
#print axioms N11Formalization.C450EighthGroupedC11.valid20
#print axioms N11Formalization.C450EighthGroupedC11.bound
#print axioms N11Formalization.C450EighthGroupedC11.endpoint_checks
