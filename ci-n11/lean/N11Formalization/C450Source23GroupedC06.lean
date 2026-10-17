import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((3345113541:ℚ)/5000000000),((861419051:ℚ)/1250000000),((-7795609561:ℚ)/12400000000),((-2641113541:ℚ)/5055000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4943168191:ℚ)/10000000000),((66702940140573092203041152848009365965366249366408440753033:ℚ)/338333407900000000000000000000000000000000000000000000000000),((514837732291794695085601343:ℚ)/1386240000000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((85120427:ℚ)/125000000),((1752675757:ℚ)/2500000000),((-15919433327:ℚ)/25275000000),((-67520427:ℚ)/128750000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((920216231:ℚ)/2000000000),((52766513247790238189144870363870126437570192565267397358471:ℚ)/267650444032690429687500000000000000000000000000000000000000),((106788741301984878758229:ℚ)/288800000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((6929016803:ℚ)/10000000000),((7070370043:ℚ)/10000000000),((-64334070473:ℚ)/103000000000),((-5521016803:ℚ)/10395000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((529202971:ℚ)/1250000000),((13202881467789141396838303301653940314279893494299171094035723:ℚ)/68330865758203125000000000000000000000000000000000000000000000),((680402874548098848174344709:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((1397739877:ℚ)/2000000000),((7130031731:ℚ)/10000000000),((-64990349041:ℚ)/103950000000),((-1116139877:ℚ)/2098000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((4038225217:ℚ)/10000000000),((2827527918731806986938907474273798573702013162787507063800049:ℚ)/14630883499725732421875000000000000000000000000000000000000000),((27154572914412398442451029:ℚ)/73932800000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-11:ℚ)/16),((-5:ℚ)/8),((220261761:ℚ)/312500000),((7159860623:ℚ)/10000000000),((-65318466853:ℚ)/104900000000),((-176261761:ℚ)/329296875),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((766694131:ℚ)/2000000000),((272537979883235603798963300850389797679298697261141047428861:ℚ)/1424161136963890625000000000000000000000000000000000000000000),((1984321558683766113410663:ℚ)/5415000000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7078212779:ℚ)/10000000000),((7189688237:ℚ)/10000000000),((-65646570607:ℚ)/105375000000),((-5670212779:ℚ)/10585000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((3727104361:ℚ)/10000000000),((174245870594484928765197217730716015983656412121251945051599479:ℚ)/910399468517294311523437500000000000000000000000000000000000000),((676536471608285753271813941:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7108047859:ℚ)/10000000000),((721951459:ℚ)/1000000000),((-6597466049:ℚ)/10585000000),((-5700047859:ℚ)/10632500000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((144710687:ℚ)/400000000),((6416152593718960896302040794341573183873692719432979107712073:ℚ)/33518407647961819726562500000000000000000000000000000000000000),((675755181048449531878378981:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((713788161:ℚ)/1000000000),((7249339699:ℚ)/10000000000),((-66302736689:ℚ)/106325000000),((-572988161:ℚ)/1068000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((7010361:ℚ)/20000000),((712027185612275414825532002711411637117742286402682449970217:ℚ)/3719171645117901611328125000000000000000000000000000000000000),((20249136607314349302023063:ℚ)/55449600000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7167714051:ℚ)/10000000000),((7279163581:ℚ)/10000000000),((-66630799391:ℚ)/106800000000),((-822816293:ℚ)/1532500000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((1694509943:ℚ)/5000000000),((713281858212395900792655768729954226439182498404226544641669:ℚ)/3725233539764062500000000000000000000000000000000000000000000),((2022553767162026559047713103:ℚ)/5544960000000000000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-11:ℚ)/16),((-5:ℚ)/8),((7197545199:ℚ)/10000000000),((7308986253:ℚ)/10000000000),((-66958848783:ℚ)/107275000000),((-5789545199:ℚ)/10775000000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((326890373:ℚ)/1000000000),((268036209535470969223746863093078159338426600998330456176631:ℚ)/1399684555932915782928466796875000000000000000000000000000000),((2020185862154340674897770103:ℚ)/5544960000000000000000000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((225855471:ℚ)/312500000),((7338807729:ℚ)/10000000000),((-67286885019:ℚ)/107750000000),((-181855471:ℚ)/338203125),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((786094527:ℚ)/2500000000),((96093460906193883526565224305927661219933474749042563191361:ℚ)/501737524470520019531250000000000000000000000000000000000000),((1970517524733660787078823:ℚ)/5415000000000000000000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((3628601843:ℚ)/5000000000),((1842157007:ℚ)/2500000000),((-16903727077:ℚ)/27056250000),((-2924601843:ℚ)/5435000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((376862003:ℚ)/1250000000),((21033292404209787945384910898589764194640126957425344210577:ℚ)/109808937696715164184570312500000000000000000000000000000000),((167952168036682397515064549:ℚ)/462080000000000000000000000)⟩
theorem valid11 : Valid source23 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source23 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((3643515529:ℚ)/5000000000),((7428265149:ℚ)/10000000000),((-68270916639:ℚ)/108700000000),((-2939515529:ℚ)/5482500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2879788297:ℚ)/10000000000),((51850662993056358647166424463223435336175888705154063874486807:ℚ)/268091732245540234375000000000000000000000000000000000000000000),((167752839596225119070760941:ℚ)/462080000000000000000000000)⟩
theorem valid12 : Valid source23 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((7346682141:ℚ)/10000000000),((7487897739:ℚ)/10000000000),((-22975625043:ℚ)/36550000000),((-848383163:ℚ)/1580000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1294567949:ℚ)/5000000000),((84650401732609834089050543127791387623664797455601830147:ℚ)/437630374276733398437500000000000000000000000000000000000),((2008226154184850589614716943:ℚ)/5544960000000000000000000000)⟩
theorem valid13 : Valid source23 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source23 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-11:ℚ)/16),((-5:ℚ)/8),((57861941:ℚ)/78125000),((950893723:ℚ)/1250000000),((-8779830953:ℚ)/13825000000),((-15620647:ℚ)/29296875),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2262391299:ℚ)/10000000000),((3177618357792403343880465519603667941321479076171521:ℚ)/16127813053131103515625000000000000000000000000000000),((40758996176706855680081:ℚ)/112812500000000000000000)⟩
theorem valid14 : Valid source23 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source23 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((3762803613:ℚ)/5000000000),((154527701:ℚ)/200000000),((-1431004711:ℚ)/2250000000),((-3058803613:ℚ)/5720000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((175040477:ℚ)/1250000000),((141406279481628434792926993482500382451337127431886461:ℚ)/717846679687500000000000000000000000000000000000000000),((498402515756257923740821007:ℚ)/1386240000000000000000000000)⟩
theorem valid15 : Valid source23 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((305794733:ℚ)/400000000),((8679752321:ℚ)/10000000000),((-82037275531:ℚ)/114400000000),((-249474733:ℚ)/518400000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((321857784464371862393358229258069359586897623220272256381:ℚ)/1325095200000000000000000000000000000000000000000000000000),((45878281:ℚ)/128000000)⟩
theorem valid16 : Valid source23 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((8598414703:ℚ)/10000000000),((2646140091:ℚ)/2500000000),((-2860837889:ℚ)/3600000000),((-7190414703:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((20473217383300121384518989287301189593560447521280297:ℚ)/72900000000000000000000000000000000000000000000000000),((45878281:ℚ)/128000000)⟩
theorem valid17 : Valid source23 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((1312934761:ℚ)/1250000000),((7195097933:ℚ)/5000000000),((-72426077263:ℚ)/80000000000),((-1136934761:ℚ)/2760000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((5914612249643783823645298217651349989117:ℚ)/16928000000000000000000000000000000000000),((45878281:ℚ)/128000000)⟩
theorem valid18 : Valid source23 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source23 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source23 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source23 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4291:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source23 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4291:ℚ)/6400) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((4291:ℚ)/6400) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source23 nn0 nn1 Qcell ((4291:ℚ)/6400) ((4329:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source23 nn0 nn1 Qcell ((4329:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source23 nn0 nn1 Qcell ((4291:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source23 nn0 nn1 Qcell ((4291:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC06
#check @N11Formalization.C450Source23GroupedC06.bound
#print axioms N11Formalization.C450Source23GroupedC06.valid0
#print axioms N11Formalization.C450Source23GroupedC06.valid1
#print axioms N11Formalization.C450Source23GroupedC06.valid2
#print axioms N11Formalization.C450Source23GroupedC06.valid3
#print axioms N11Formalization.C450Source23GroupedC06.valid4
#print axioms N11Formalization.C450Source23GroupedC06.valid5
#print axioms N11Formalization.C450Source23GroupedC06.valid6
#print axioms N11Formalization.C450Source23GroupedC06.valid7
#print axioms N11Formalization.C450Source23GroupedC06.valid8
#print axioms N11Formalization.C450Source23GroupedC06.valid9
#print axioms N11Formalization.C450Source23GroupedC06.valid10
#print axioms N11Formalization.C450Source23GroupedC06.valid11
#print axioms N11Formalization.C450Source23GroupedC06.valid12
#print axioms N11Formalization.C450Source23GroupedC06.valid13
#print axioms N11Formalization.C450Source23GroupedC06.valid14
#print axioms N11Formalization.C450Source23GroupedC06.valid15
#print axioms N11Formalization.C450Source23GroupedC06.valid16
#print axioms N11Formalization.C450Source23GroupedC06.valid17
#print axioms N11Formalization.C450Source23GroupedC06.valid18
#print axioms N11Formalization.C450Source23GroupedC06.bound
#print axioms N11Formalization.C450Source23GroupedC06.endpoint_checks
