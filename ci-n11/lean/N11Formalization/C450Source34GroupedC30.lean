import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((13:ℚ)/16),((7:ℚ)/8),((5011978593:ℚ)/10000000000),((5354107153:ℚ)/10000000000),((85635721709:ℚ)/103000000000),((48038750071:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((8506816699:ℚ)/10000000000),((-1003427360979486547004631428963557199843:ℚ)/3142116352000000000000000000000000000000),((-7981662001443351634480785421:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((5250703023:ℚ)/10000000000),((2796580507:ℚ)/5000000000),((88739139299:ℚ)/106800000000),((24856063549:ℚ)/25750000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((8080880447:ℚ)/10000000000),((-36092257568821515371339793066585712615166918052637869991:ℚ)/111296886062622070312500000000000000000000000000000000000),((-1967523380152449749220500581:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((2744669847:ℚ)/5000000000),((2856323411:ℚ)/5000000000),((45920708011:ℚ)/54350000000),((283980493:ℚ)/300000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3818503667:ℚ)/5000000000),((-191103161518214964556399657617277114063691731524335921:ℚ)/550293750000000000000000000000000000000000000000000000),((-1953443663661458838443511349:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((5608628023:ℚ)/10000000000),((5832107121:ℚ)/10000000000),((13341737757:ℚ)/15800000000),((51384749847:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((7407281633:ℚ)/10000000000),((-1727282848447247806939749136970490216171884083033633924209:ℚ)/4954339586767578125000000000000000000000000000000000000000),((-23271296409691020227653642087:ℚ)/44359680000000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((2863948867:ℚ)/5000000000),((5891828117:ℚ)/10000000000),((47471335271:ℚ)/55775000000),((51802796819:ℚ)/55300000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((7171669881:ℚ)/10000000000),((-120830338232549259177488516689341182538556606602762475733539:ℚ)/336865815256250000000000000000000000000000000000000000000000),((-7728626884926350448348428741:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((13:ℚ)/16),((7:ℚ)/8),((1446881477:ℚ)/2500000000),((297577161:ℚ)/500000000),((23929459201:ℚ)/28125000000),((2611040127:ℚ)/2788750000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((440716601:ℚ)/625000000),((-19051270007849672243402312054071499255615955512115617:ℚ)/53042433508300781250000000000000000000000000000000000),((-57750491817237005057549047:ℚ)/110899200000000000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((5847149779:ℚ)/10000000000),((6011252579:ℚ)/10000000000),((96492947127:ℚ)/113450000000),((52638768053:ℚ)/56250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6929547969:ℚ)/10000000000),((-907695487986654040599067212115483004910722933457917076608801:ℚ)/2523957824707031250000000000000000000000000000000000000000000),((-7671414831030537672750033429:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((13:ℚ)/16),((7:ℚ)/8),((369173091:ℚ)/625000000),((6041105149:ℚ)/10000000000),((6079250183:ℚ)/7120312500),((52847736043:ℚ)/56725000000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((850727743:ℚ)/1250000000),((-10821412171860790287790401350249524889255720226561299374009:ℚ)/29706022859214843750000000000000000000000000000000000000000),((-7657055907382069472338707669:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((1187315551:ℚ)/2000000000),((3035478169:ℚ)/5000000000),((19531102163:ℚ)/22880000000),((26528347183:ℚ)/28481250000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((6743248833:ℚ)/10000000000),((-268781548016638300620349156080437022376366280887697404871:ℚ)/737454383147048950195312500000000000000000000000000000000),((-1910668652073918040397140509:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((13:ℚ)/16),((7:ℚ)/8),((1193277009:ℚ)/2000000000),((6100806161:ℚ)/10000000000),((19608601117:ℚ)/22975000000),((53265643127:ℚ)/57200000000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((3340092067:ℚ)/5000000000),((-293987752882643457798402272255931705394243700422752889540483:ℚ)/806203869900000000000000000000000000000000000000000000000000),((-7628270929725054054517838349:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((5996191339:ℚ)/10000000000),((6130654637:ℚ)/10000000000),((32810162469:ℚ)/38450000000),((53474582459:ℚ)/57437500000),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((6616613429:ℚ)/10000000000),((-83067796940272374774148230822577499304302316347909960370187:ℚ)/227684230373764038085937500000000000000000000000000000000000),((-7613844865642688686780382261:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2307:ℚ)/3200),((4633:ℚ)/6400),((13:ℚ)/16),((7:ℚ)/8),((753249581:ℚ)/1250000000),((3080250891:ℚ)/5000000000),((12352244553:ℚ)/14478125000),((8947252079:ℚ)/9612500000),((1905827251:ℚ)/2000000000),((1907725537:ℚ)/2000000000),((3080928657:ℚ)/10000000000),((6552521627:ℚ)/10000000000),((-375510336833172272103922341899161596084222428571042462471:ℚ)/1028753598387207031250000000000000000000000000000000000000),((-5699547308561743819933562767:ℚ)/11089920000000000000000000000)⟩
theorem valid11 : Valid source34 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source34 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_of_packet source34 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4633:ℚ)/6400),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((1211160197:ℚ)/2000000000),((6190347613:ℚ)/10000000000),((19841082561:ℚ)/23260000000),((53892433291:ℚ)/57912500000),((9519843613:ℚ)/10000000000),((476456813:ℚ)/500000000),((622285377:ℚ)/2000000000),((162197323:ℚ)/250000000),((-1288942376799287809230119846709997863882658670749830841609:ℚ)/3529528396952239990234375000000000000000000000000000000000),((-7584925561876279464875706261:ℚ)/14786560000000000000000000000)⟩
theorem valid12 : Valid source34 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source34 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1163:ℚ)/1600),((4671:ℚ)/6400),((13:ℚ)/16),((7:ℚ)/8),((3042802181:ℚ)/5000000000),((1244038429:ℚ)/2000000000),((16598809451:ℚ)/19462500000),((10820269003:ℚ)/11630000000),((148605427:ℚ)/156250000),((4759921809:ℚ)/5000000000),((98156347:ℚ)/312500000),((6422710733:ℚ)/10000000000),((-1398190976585730064125665896277790684783748368049656445663:ℚ)/3826905893873437500000000000000000000000000000000000000000),((-302817292511051256533412629:ℚ)/591462400000000000000000000)⟩
theorem valid13 : Valid source34 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((4671:ℚ)/6400) :=
  cell_of_packet source34 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4671:ℚ)/6400),((469:ℚ)/640),((13:ℚ)/16),((7:ℚ)/8),((6115406791:ℚ)/10000000000),((3125017697:ℚ)/5000000000),((99980288283:ℚ)/117250000000),((27155123879:ℚ)/29193750000),((9501845013:ℚ)/10000000000),((9510747333:ℚ)/10000000000),((792422551:ℚ)/2500000000),((6356957673:ℚ)/10000000000),((-11425152875357057047208001545839932370418577442461609289447:ℚ)/31256887429673767089843750000000000000000000000000000000000),((-1888979164833545485529375021:ℚ)/3696640000000000000000000000)⟩
theorem valid14 : Valid source34 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source34 nn0 nn1 Qcell ((4671:ℚ)/6400) ((469:ℚ)/640) :=
  cell_of_packet source34 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((13:ℚ)/16),((7:ℚ)/8),((6145208283:ℚ)/10000000000),((3139938689:ℚ)/5000000000),((100367707679:ℚ)/117725000000),((27259570823:ℚ)/29312500000),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((629061547:ℚ)/1000000000),((-67766794631508223590426341814696118746153787951270963316251:ℚ)/185313601562881469726562500000000000000000000000000000000000),((-5222561354393268742622309:ℚ)/10240000000000000000000000)⟩
theorem valid15 : Valid source34 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source34 nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet source34 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6175008851:ℚ)/10000000000),((6309718109:ℚ)/10000000000),((100755115063:ℚ)/118200000000),((54728026763:ℚ)/58862500000),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((6223664911:ℚ)/10000000000),((-68900517651434264647558200213263675061753891068897305979941:ℚ)/188331782659725952148437500000000000000000000000000000000000),((-7526818119073549653115485589:ℚ)/14786560000000000000000000000)⟩
theorem valid16 : Valid source34 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source34 nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((13:ℚ)/16),((7:ℚ)/8),((775601063:ℚ)/1250000000),((1267911521:ℚ)/2000000000),((12642813819:ℚ)/14834375000),((10987380647:ℚ)/11820000000),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((307804289:ℚ)/500000000),((-273080533682747880650199624284062531675847653942102056947:ℚ)/746116608150000000000000000000000000000000000000000000000),((-300489408936785077583165229:ℚ)/591462400000000000000000000)⟩
theorem valid17 : Valid source34 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet source34 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((3117303627:ℚ)/5000000000),((159234897:ℚ)/250000000),((50764947151:ℚ)/59575000000),((29332857:ℚ)/31562500),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((47561381:ℚ)/78125000),((-42867039279911135725250310780653882068003220487347:ℚ)/117073406362533569335937500000000000000000000000000),((-14058056071466914619722663:ℚ)/27724800000000000000000000)⟩
theorem valid18 : Valid source34 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source34 nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((2383:ℚ)/3200),((957:ℚ)/1280),((13:ℚ)/16),((7:ℚ)/8),((6264405113:ℚ)/10000000000),((1599808237:ℚ)/2500000000),((101917266469:ℚ)/119625000000),((13838657659:ℚ)/14893750000),((75681297:ℚ)/80000000),((2367032267:ℚ)/2500000000),((1650403157:ℚ)/5000000000),((3009477699:ℚ)/5000000000),((-452404269443111724817372220365546254618843479259320077519:ℚ)/1235048895250225067138671875000000000000000000000000000000),((-467687634944916007367303861:ℚ)/924160000000000000000000000)⟩
theorem valid19 : Valid source34 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source34 nn0 nn1 Qcell ((2383:ℚ)/3200) ((957:ℚ)/1280) :=
  cell_of_packet source34 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((957:ℚ)/1280),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((629420209:ℚ)/1000000000),((803633603:ℚ)/1250000000),((10230462717:ℚ)/12010000000),((6945435221:ℚ)/7476562500),((4726187811:ℚ)/5000000000),((946016213:ℚ)/1000000000),((831186567:ℚ)/2500000000),((371834871:ℚ)/625000000),((-1277328083631976655128524554439353046255927388302158657:ℚ)/3485671212583780288696289062500000000000000000000000000),((-116692999716417660823483221:ℚ)/231040000000000000000000000)⟩
theorem valid20 : Valid source34 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source34 nn0 nn1 Qcell ((957:ℚ)/1280) ((1201:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((6323998197:ℚ)/10000000000),((6488737057:ℚ)/10000000000),((102691976561:ℚ)/121050000000),((55981159399:ℚ)/60050000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((5879039277:ℚ)/10000000000),((-1188464290196099582594022152879597223077234772421145902994587:ℚ)/3276527685953906250000000000000000000000000000000000000000000),((-7438984315437879226969310381:ℚ)/14786560000000000000000000000)⟩
theorem valid21 : Valid source34 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source34 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((6383587839:ℚ)/10000000000),((654840069:ℚ)/1000000000),((103466641907:ℚ)/122000000000),((626653387:ℚ)/672500000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((5736130473:ℚ)/10000000000),((-42096125267120204523028637795148253368719822503562799:ℚ)/115954262597656250000000000000000000000000000000000000),((-222285806173737450684466927:ℚ)/443596800000000000000000000)⟩
theorem valid22 : Valid source34 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source34 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source34 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((161079353:ℚ)/250000000),((6608059831:ℚ)/10000000000),((2606031589:ℚ)/3073750000),((56816418817:ℚ)/61000000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((5589996327:ℚ)/10000000000),((-316877118084521650453927962951817354060173569537904298652971:ℚ)/872103560937500000000000000000000000000000000000000000000000),((-7379979620626486639312704509:ℚ)/14786560000000000000000000000)⟩
theorem valid23 : Valid source34 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((5080279:ℚ)/7812500),((833464323:ℚ)/1250000000),((82043627:ℚ)/96796875),((7154250261:ℚ)/7684375000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((4352299:ℚ)/8000000),((-182538335361866661791766037660283362433378720979610528301:ℚ)/501971355148887634277343750000000000000000000000000000000),((-344547306046013700962328703:ℚ)/693120000000000000000000000)⟩
theorem valid24 : Valid source34 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source34 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6562336913:ℚ)/10000000000),((271480453:ℚ)/400000000),((105790379869:ℚ)/125800000000),((2322763171:ℚ)/2478000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((660870419:ℚ)/1250000000),((-20824326396245422895255307232702520109055143449961463:ℚ)/58416376174365234375000000000000000000000000000000000),((-11665277932319123828691621:ℚ)/23658496000000000000000000)⟩
theorem valid25 : Valid source34 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source34 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((6681487173:ℚ)/10000000000),((17563891:ℚ)/25000000),((107339333249:ℚ)/129600000000),((149347237:ℚ)/157250000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((4967353293:ℚ)/10000000000),((-674172767745375454248160406531296933546960901640581:ℚ)/1968507159082031250000000000000000000000000000000000),((-44816448248259998841589:ℚ)/92416000000000000000000)⟩
theorem valid26 : Valid source34 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source34 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((81:ℚ)/100),((343:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((1729938079:ℚ)/2500000000),((3751235917:ℚ)/5000000000),((27609195027:ℚ)/34300000000),((31538651419:ℚ)/32400000000),((57977633:ℚ)/62500000),((2332870371:ℚ)/2500000000),((1913736159:ℚ)/5000000000),((2131599399:ℚ)/5000000000),((-616454363364425959173034547430883221712669930278942293201:ℚ)/1953045675000000000000000000000000000000000000000000000000),((-1731493680752452489822087541:ℚ)/3696640000000000000000000000)⟩
theorem valid27 : Valid source34 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((343:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((343:ℚ)/400),((181:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((739615489:ℚ)/1000000000),((797918511:ℚ)/1000000000),((11663001357:ℚ)/14480000000),((6641429577:ℚ)/6860000000),((9252071821:ℚ)/10000000000),((1855284257:ℚ)/2000000000),((1946075537:ℚ)/5000000000),((580328473:ℚ)/2500000000),((-668982221662413359506802066175351060394318833646768827:ℚ)/2086857962000000000000000000000000000000000000000000000),((-19044927:ℚ)/40960000)⟩
theorem valid28 : Valid source34 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source34 nn0 nn1 Qcell ((343:ℚ)/400) ((181:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((492025603:ℚ)/625000000),((8932121141:ℚ)/10000000000),((7676332839:ℚ)/10000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-1746901973789040937636657:ℚ)/6250000000000000000000000),((-19044927:ℚ)/40960000)⟩
theorem valid29 : Valid source34 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source34 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet29 valid29
def packet30 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((8824560359:ℚ)/10000000000),((6369905661:ℚ)/5000000000),((135199284667:ℚ)/220800000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-41019827686221269:ℚ)/220800000000000000),((-19044927:ℚ)/40960000)⟩
theorem valid30 : Valid source34 packet30 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf30 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet30 valid30
private theorem node1_3 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source34 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2269:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source34 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source34 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source34 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source34 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source34 nn0 nn1 Qcell ((2269:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_7 node7_15
private theorem node15_17 :
    CellBound source34 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_join leaf15 leaf16
private theorem node17_19 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_join leaf17 leaf18
private theorem node15_19 :
    CellBound source34 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join node15_17 node17_19
private theorem node19_21 :
    CellBound source34 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join leaf19 leaf20
private theorem node21_23 :
    CellBound source34 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf21 leaf22
private theorem node19_23 :
    CellBound source34 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join node19_21 node21_23
private theorem node15_23 :
    CellBound source34 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node15_19 node19_23
private theorem node23_25 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf23 leaf24
private theorem node25_27 :
    CellBound source34 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf25 leaf26
private theorem node23_27 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join node23_25 node25_27
private theorem node27_29 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_join leaf27 leaf28
private theorem node29_31 :
    CellBound source34 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf29 leaf30
private theorem node27_31 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join node27_29 node29_31
private theorem node23_31 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node23_27 node27_31
private theorem node15_31 :
    CellBound source34 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node15_23 node23_31
private theorem node0_31 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_15 node15_31
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_31
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29,packet30]
theorem packet_count : packets.length = 31 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC30
#check @N11Formalization.C450Source34GroupedC30.bound
#print axioms N11Formalization.C450Source34GroupedC30.valid0
#print axioms N11Formalization.C450Source34GroupedC30.valid1
#print axioms N11Formalization.C450Source34GroupedC30.valid2
#print axioms N11Formalization.C450Source34GroupedC30.valid3
#print axioms N11Formalization.C450Source34GroupedC30.valid4
#print axioms N11Formalization.C450Source34GroupedC30.valid5
#print axioms N11Formalization.C450Source34GroupedC30.valid6
#print axioms N11Formalization.C450Source34GroupedC30.valid7
#print axioms N11Formalization.C450Source34GroupedC30.valid8
#print axioms N11Formalization.C450Source34GroupedC30.valid9
#print axioms N11Formalization.C450Source34GroupedC30.valid10
#print axioms N11Formalization.C450Source34GroupedC30.valid11
#print axioms N11Formalization.C450Source34GroupedC30.valid12
#print axioms N11Formalization.C450Source34GroupedC30.valid13
#print axioms N11Formalization.C450Source34GroupedC30.valid14
#print axioms N11Formalization.C450Source34GroupedC30.valid15
#print axioms N11Formalization.C450Source34GroupedC30.valid16
#print axioms N11Formalization.C450Source34GroupedC30.valid17
#print axioms N11Formalization.C450Source34GroupedC30.valid18
#print axioms N11Formalization.C450Source34GroupedC30.valid19
#print axioms N11Formalization.C450Source34GroupedC30.valid20
#print axioms N11Formalization.C450Source34GroupedC30.valid21
#print axioms N11Formalization.C450Source34GroupedC30.valid22
#print axioms N11Formalization.C450Source34GroupedC30.valid23
#print axioms N11Formalization.C450Source34GroupedC30.valid24
#print axioms N11Formalization.C450Source34GroupedC30.valid25
#print axioms N11Formalization.C450Source34GroupedC30.valid26
#print axioms N11Formalization.C450Source34GroupedC30.valid27
#print axioms N11Formalization.C450Source34GroupedC30.valid28
#print axioms N11Formalization.C450Source34GroupedC30.valid29
#print axioms N11Formalization.C450Source34GroupedC30.valid30
#print axioms N11Formalization.C450Source34GroupedC30.bound
#print axioms N11Formalization.C450Source34GroupedC30.endpoint_checks
