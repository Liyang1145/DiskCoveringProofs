import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/4),((13:ℚ)/16),((317472571:ℚ)/625000000),((677697921:ℚ)/1250000000),((1272417713:ℚ)/1609375000),((11450072973:ℚ)/12400000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1677580129:ℚ)/2000000000),((-16431317710586457519889611608385666121:ℚ)/49095568000000000000000000000000000000),((-1882131111840611714172339:ℚ)/3610000000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((212753711:ℚ)/400000000),((2830544707:ℚ)/5000000000),((9472597:ℚ)/12000000),((47357081191:ℚ)/51500000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((3978060119:ℚ)/5000000000),((-3383502044148445838835974111846118289925508493721082901:ℚ)/10004214477539062500000000000000000000000000000000000000),((-29672443625782055366871271:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((2778998151:ℚ)/5000000000),((1445197301:ℚ)/2500000000),((10896994453:ℚ)/13587500000),((24067564913:ℚ)/26700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3752739401:ℚ)/5000000000),((-138677128445391541211273855686381801389696242056255720274941:ℚ)/387940034643750000000000000000000000000000000000000000000000),((-7361882990279928303499279:ℚ)/14440000000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((17742279:ℚ)/31250000),((2950227991:ℚ)/5000000000),((69226837:ℚ)/86406250),((48912963883:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3635965309:ℚ)/5000000000),((-5326027053952397217748380254057750263486341993291655466063:ℚ)/14863018760302734375000000000000000000000000000000000000000),((-29219895807374004625815199:ℚ)/57760000000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((2898517549:ℚ)/5000000000),((5960277527:ℚ)/10000000000),((11255552647:ℚ)/13943750000),((14086229693:ℚ)/15800000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((7032139211:ℚ)/10000000000),((-20172065968748240493412274351322343343086835517860198109979:ℚ)/54998500450000000000000000000000000000000000000000000000000),((-116420222946241268829395791:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((3:ℚ)/4),((13:ℚ)/16),((2928389131:ℚ)/5000000000),((3010045723:ℚ)/5000000000),((11345167393:ℚ)/14062500000),((49690594399:ℚ)/55775000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6909692039:ℚ)/10000000000),((-155753575494858220218185913993865449364432440163510628801:ℚ)/424339468066406250000000000000000000000000000000000000000),((-28989534181032907000448791:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((5916515151:ℚ)/10000000000),((3039948967:ℚ)/5000000000),((22869545453:ℚ)/28362500000),((50079336571:ℚ)/56250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((3392708699:ℚ)/5000000000),((-927079819878366993914617884717408399207066442981750549738543:ℚ)/2523957824707031250000000000000000000000000000000000000000000),((-28873331027016079882711231:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((1494061481:ℚ)/2500000000),((6139697179:ℚ)/10000000000),((5762184443:ℚ)/7150000000),((100936063327:ℚ)/113450000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((53273679:ℚ)/80000000),((-19187620971584139320854478988397268429073376289179209772153:ℚ)/52202289018343750000000000000000000000000000000000000000000),((-115025784661393373422028039:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((6035970737:ℚ)/10000000000),((3099744681:ℚ)/5000000000),((23227912211:ℚ)/28837500000),((4623334623:ℚ)/5200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1306190859:ℚ)/2000000000),((-186420041847863700328633584595683492184141935358937892317:ℚ)/506847900000000000000000000000000000000000000000000000000),((-28638879491892350813417919:ℚ)/57760000000000000000000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((6095689737:ℚ)/10000000000),((6259274659:ℚ)/10000000000),((23407069211:ℚ)/29075000000),((102490570567:ℚ)/115350000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1280104883:ℚ)/2000000000),((-54744067145582799926921773367241387580562028553964423911759:ℚ)/148748044575093750000000000000000000000000000000000000000000),((-114082523615908899256670999:ℚ)/231040000000000000000000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/4),((13:ℚ)/16),((6155403069:ℚ)/10000000000),((6319053239:ℚ)/10000000000),((23586209207:ℚ)/29312500000),((103267692107:ℚ)/116300000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3133890673:ℚ)/5000000000),((-181928179534225701975711108649463966692641632879094582087931:ℚ)/494032167417187500000000000000000000000000000000000000000000),((-113606801218729775108105359:ℚ)/231040000000000000000000000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((6215110873:ℚ)/10000000000),((3189412633:ℚ)/5000000000),((23765332619:ℚ)/29550000000),((52022364229:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((766571463:ℚ)/1250000000),((-68556474024081003593031865454549973199394305661572869792283:ℚ)/186061309872436523437500000000000000000000000000000000000000),((-28282087599233268136113631:ℚ)/57760000000000000000000000)⟩
theorem valid11 : Valid source34 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source34 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((3137406641:ℚ)/5000000000),((64385909:ℚ)/100000000),((11972219923:ℚ)/14893750000),((1048216817:ℚ)/1182000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((5994725399:ℚ)/10000000000),((-138083196739964640605388848772889842340648541317359473:ℚ)/374551480350000000000000000000000000000000000000000000),((-11264717077310012305999:ℚ)/23104000000000000000000)⟩
theorem valid12 : Valid source34 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((1583627607:ℚ)/2500000000),((6498350293:ℚ)/10000000000),((6030882821:ℚ)/7506250000),((105598553809:ℚ)/119150000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1170810589:ℚ)/2000000000),((-292712459586879099491836439116613577911751587828808324619017:ℚ)/793569891615576171875000000000000000000000000000000000000000),((-112163262004914441201751271:ℚ)/231040000000000000000000000)⟩
theorem valid13 : Valid source34 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source34 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((1598550609:ℚ)/2500000000),((1639525899:ℚ)/2500000000),((6075651827:ℚ)/7565625000),((26593836687:ℚ)/30025000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((285517111:ℚ)/500000000),((-151146082126769834279619568826155756205861311747221540577139:ℚ)/409565960744238281250000000000000000000000000000000000000000),((-6979788983116129003943679:ℚ)/14440000000000000000000000)⟩
theorem valid14 : Valid source34 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source34 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((645388943:ℚ)/1000000000),((6617850951:ℚ)/10000000000),((2448166829:ℚ)/3050000000),((11905784707:ℚ)/13450000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((222534179:ℚ)/400000000),((-342497602781875483179731679295974134856729569697504492919:ℚ)/927634100781250000000000000000000000000000000000000000000),((-111187255631162314381378479:ℚ)/231040000000000000000000000)⟩
theorem valid15 : Valid source34 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source34 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source34 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((6513571527:ℚ)/10000000000),((3368664187:ℚ)/5000000000),((24660714581:ℚ)/30975000000),((54352634431:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1082563881:ℚ)/2000000000),((-22773760789530833082417148556329870200497808013598099108191:ℚ)/62774432812500000000000000000000000000000000000000000000000),((-27550082163671549745921751:ℚ)/57760000000000000000000000)⟩
theorem valid16 : Valid source34 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((3316460743:ℚ)/5000000000),((1714195907:ℚ)/2500000000),((12509382229:ℚ)/15725000000),((27564546791:ℚ)/30975000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((5099829581:ℚ)/10000000000),((-41444364788387352734392244596860148465586181460466212643:ℚ)/114094484715557098388671875000000000000000000000000000000),((-6825154912663311499543471:ℚ)/14440000000000000000000000)⟩
theorem valid17 : Valid source34 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source34 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((1688063297:ℚ)/2500000000),((7095631573:ℚ)/10000000000),((6344189891:ℚ)/8100000000),((113363210449:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2384149313:ℚ)/5000000000),((-353723484485397170210527297832491313500894791757656838234873:ℚ)/1007875665450000000000000000000000000000000000000000000000000),((-107174000139845483989545191:ℚ)/231040000000000000000000000)⟩
theorem valid18 : Valid source34 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source34 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((6990865067:ℚ)/10000000000),((8050310763:ℚ)/10000000000),((26092595201:ℚ)/36200000000),((41924679973:ℚ)/43200000000),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((503870879:ℚ)/1250000000),((-4733701086092471719378475525849881768696205776084584387947:ℚ)/17100590400000000000000000000000000000000000000000000000000),((-56922247:ℚ)/128000000)⟩
theorem valid19 : Valid source34 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((7944725527:ℚ)/10000000000),((4502047773:ℚ)/5000000000),((28954176581:ℚ)/40000000000),((69086621049:ℚ)/72400000000),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-172090566455793445544889379217007456369451452464305450393:ℚ)/592974100000000000000000000000000000000000000000000000000),((-56922247:ℚ)/128000000)⟩
theorem valid20 : Valid source34 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source34 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((177956977:ℚ)/200000000),((1601750563:ℚ)/1250000000),((636270931:ℚ)/1104000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-185800216176317:ℚ)/1104000000000000),((-56922247:ℚ)/128000000)⟩
theorem valid21 : Valid source34 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet21 valid21
private theorem node0_2 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((2231:ℚ)/3200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source34 nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source34 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source34 nn0 nn1 Qcell ((2231:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_5 node5_11
private theorem node11_13 :
    CellBound source34 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf11 leaf12
private theorem node14_16 :
    CellBound source34 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source34 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf13 node14_16
private theorem node11_16 :
    CellBound source34 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node11_13 node13_16
private theorem node17_19 :
    CellBound source34 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf16 node17_19
private theorem node20_22 :
    CellBound source34 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf19 node20_22
private theorem node16_22 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node16_19 node19_22
private theorem node11_22 :
    CellBound source34 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node11_16 node16_22
private theorem node0_22 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_22
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_22
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21]
theorem packet_count : packets.length = 22 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC29
#check @N11Formalization.C450Source34GroupedC29.bound
#print axioms N11Formalization.C450Source34GroupedC29.valid0
#print axioms N11Formalization.C450Source34GroupedC29.valid1
#print axioms N11Formalization.C450Source34GroupedC29.valid2
#print axioms N11Formalization.C450Source34GroupedC29.valid3
#print axioms N11Formalization.C450Source34GroupedC29.valid4
#print axioms N11Formalization.C450Source34GroupedC29.valid5
#print axioms N11Formalization.C450Source34GroupedC29.valid6
#print axioms N11Formalization.C450Source34GroupedC29.valid7
#print axioms N11Formalization.C450Source34GroupedC29.valid8
#print axioms N11Formalization.C450Source34GroupedC29.valid9
#print axioms N11Formalization.C450Source34GroupedC29.valid10
#print axioms N11Formalization.C450Source34GroupedC29.valid11
#print axioms N11Formalization.C450Source34GroupedC29.valid12
#print axioms N11Formalization.C450Source34GroupedC29.valid13
#print axioms N11Formalization.C450Source34GroupedC29.valid14
#print axioms N11Formalization.C450Source34GroupedC29.valid15
#print axioms N11Formalization.C450Source34GroupedC29.valid16
#print axioms N11Formalization.C450Source34GroupedC29.valid17
#print axioms N11Formalization.C450Source34GroupedC29.valid18
#print axioms N11Formalization.C450Source34GroupedC29.valid19
#print axioms N11Formalization.C450Source34GroupedC29.valid20
#print axioms N11Formalization.C450Source34GroupedC29.valid21
#print axioms N11Formalization.C450Source34GroupedC29.bound
#print axioms N11Formalization.C450Source34GroupedC29.endpoint_checks
