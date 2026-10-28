import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((2003:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((174724533:ℚ)/250000000),((7150454017:ℚ)/10000000000),((-18507362051:ℚ)/19840000000),((-1031071731:ℚ)/1251875000),((398569427:ℚ)/400000000),(1:ℚ),((845998389:ℚ)/10000000000),((4037281023:ℚ)/10000000000),((11655440402538911129913050497323922874524007:ℚ)/39164890355793920000000000000000000000000000),((530454611086379799053521347:ℚ)/591462400000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((2003:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((2003:ℚ)/3200),((1011:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((3524254329:ℚ)/5000000000),((3604956481:ℚ)/5000000000),((-9342869443:ℚ)/10015000000),((-6943260101:ℚ)/8425000000),((9929701407:ℚ)/10000000000),((62276473:ℚ)/62500000),((18538009:ℚ)/156250000),((958251297:ℚ)/2500000000),((8281453822035963461175921312752239058213287077250484817:ℚ)/27851764520030609130859375000000000000000000000000000000),((133043790551735900161185603:ℚ)/147865600000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((2003:ℚ)/3200) ((1011:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1011:ℚ)/1600),((4063:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((3554016561:ℚ)/5000000000),((1447928369:ℚ)/2000000000),((-3754985107:ℚ)/4044000000),((-1237536231:ℚ)/1493750000),((4956442379:ℚ)/5000000000),((2482425353:ℚ)/2500000000),((1320924081:ℚ)/10000000000),((90445549:ℚ)/250000000),((143416468426585206390262990869687232208059737842976022379:ℚ)/491890032925425000000000000000000000000000000000000000000),((21321459285888316427052003:ℚ)/23658496000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4063:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4063:ℚ)/6400),((2041:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7137794301:ℚ)/10000000000),((3634685171:ℚ)/5000000000),((-9432055513:ℚ)/10157500000),((-42284560107:ℚ)/51025000000),((247409071:ℚ)/250000000),((9912884763:ℚ)/10000000000),((1440948769:ℚ)/10000000000),((1752757519:ℚ)/5000000000),((47058949817906064604337407272759472476002910541688181989067:ℚ)/161450656443408496093750000000000000000000000000000000000000),((133474624626608465790054843:ℚ)/147865600000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((4063:ℚ)/6400) ((2041:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2041:ℚ)/3200),((8183:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((895944349:ℚ)/1250000000),((7284234447:ℚ)/10000000000),((-18908703341:ℚ)/20410000000),((-5311610443:ℚ)/6392968750),((9888211123:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((37416203:ℚ)/250000000),((67793003:ℚ)/200000000),((9213834124673190893939302545178914063127484140345403327181:ℚ)/31919542118122750000000000000000000000000000000000000000000),((534329767870819216698446307:ℚ)/591462400000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((2041:ℚ)/3200) ((8183:ℚ)/12800) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((8183:ℚ)/12800),((4101:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7182434783:ℚ)/10000000000),((7299098457:ℚ)/10000000000),((-18953295371:ℚ)/20457500000),((-42597043481:ℚ)/51262500000),((4940065779:ℚ)/5000000000),((1236026391:ℚ)/1250000000),((774947369:ℚ)/5000000000),((416283461:ℚ)/1250000000),((193264390293382981639329391258713428920132282134059886331501:ℚ)/669603888089216532897949218750000000000000000000000000000000),((534761211373186742472814227:ℚ)/591462400000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((8183:ℚ)/12800) ((4101:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4101:ℚ)/6400),((8221:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((1439462921:ℚ)/2000000000),((3656981187:ℚ)/5000000000),((-9498943561:ℚ)/10252500000),((-8540240447:ℚ)/10276250000),((4936061823:ℚ)/5000000000),((9880131563:ℚ)/10000000000),((320187229:ℚ)/2000000000),((1634924259:ℚ)/5000000000),((43790683236876763688631470260665734423861093945538244096528073:ℚ)/151739061245239555371093750000000000000000000000000000000000000),((133798207267058128132656987:ℚ)/147865600000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((4101:ℚ)/6400) ((8221:ℚ)/12800) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((8221:ℚ)/12800),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((7212194259:ℚ)/10000000000),((3664413099:ℚ)/5000000000),((-9521239297:ℚ)/10276250000),((-42805359813:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((9872123651:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((3208333999:ℚ)/10000000000),((20763164523765586502091558337859421117996026276252740825467:ℚ)/71954581300382678222656250000000000000000000000000000000000),((133906155238159055403567723:ℚ)/147865600000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((8221:ℚ)/12800) ((103:ℚ)/160) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((103:ℚ)/160),((8259:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7227073747:ℚ)/10000000000),((7343689929:ℚ)/10000000000),((-19087069787:ℚ)/20600000000),((-42909516229:ℚ)/51618750000),((9856320801:ℚ)/10000000000),((616511681:ℚ)/625000000),((1697201141:ℚ)/10000000000),((3145659793:ℚ)/10000000000),((1400108074616970392012370332241743280864935541613237120853771:ℚ)/4852610020044726562500000000000000000000000000000000000000000),((536056587023077585240488243:ℚ)/591462400000000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((8259:ℚ)/12800) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8259:ℚ)/12800),((4139:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7241953071:ℚ)/10000000000),((229954799:ℚ)/312500000),((-597864397:ℚ)/645234375),((-43013671497:ℚ)/51737500000),((984852489:ℚ)/1000000000),((4928160403:ℚ)/5000000000),((1742751127:ℚ)/10000000000),((3081755069:ℚ)/10000000000),((2765920246950535009899926142125282168159891128559167816801:ℚ)/9587427764490564921498298645019531250000000000000000000000),((523914772759097600519523:ℚ)/577600000000000000000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((8259:ℚ)/12800) ((4139:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4139:ℚ)/6400),((8297:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((725683223:ℚ)/1000000000),((1843354279:ℚ)/2500000000),((-4794062837:ℚ)/5173750000),((-4311782561:ℚ)/5185625000),((9840798677:ℚ)/10000000000),((1969704979:ℚ)/2000000000),((1786759881:ℚ)/10000000000),((1508270777:ℚ)/5000000000),((687523797845086950974285028334970798497600600879417584423167:ℚ)/2383408627518712095214843750000000000000000000000000000000000),((33557565114072391046378643:ℚ)/36966400000000000000000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((4139:ℚ)/6400) ((8297:ℚ)/12800) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8297:ℚ)/12800),((2079:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7271711227:ℚ)/10000000000),((7388280573:ℚ)/10000000000),((-19220841719:ℚ)/20742500000),((-43221978589:ℚ)/51975000000),((4916570841:ℚ)/5000000000),((4920399341:ℚ)/5000000000),((1829340989:ℚ)/10000000000),((737483091:ℚ)/2500000000),((39419845340548133708147829932223532984822135205819588116949:ℚ)/136670162722887524414062500000000000000000000000000000000000),((537353530579355706481890267:ℚ)/591462400000000000000000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell ((8297:ℚ)/12800) ((2079:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((3643295031:ℚ)/5000000000),((3709003609:ℚ)/5000000000),((-125389751:ℚ)/135000000),((-21663065217:ℚ)/26106250000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((360228831:ℚ)/1250000000),((8676644249854598912577239141883245663212490277361940909:ℚ)/29810397283593750000000000000000000000000000000000000000),((134554757723582412669436563:ℚ)/147865600000000000000000000)⟩
theorem valid12 : Valid source25 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source25 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((1829086813:ℚ)/2500000000),((1861933377:ℚ)/2500000000),((-4849800131:ℚ)/5221250000),((-10883607691:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((2740701851:ℚ)/10000000000),((284852115289370582782530288351587150095684145187500208602569:ℚ)/978936357801348059082031250000000000000000000000000000000000),((33692826773143014907193667:ℚ)/36966400000000000000000000)⟩
theorem valid13 : Valid source25 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source25 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-15:ℚ)/16),((-7:ℚ)/8),((14347859:ℚ)/19531250),((934682431:ℚ)/1250000000),((-2436047293:ℚ)/2622500000),((-1366960208:ℚ)/1646484375),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((648026599:ℚ)/2500000000),((23303924935515934429141208060671725898804374989889534812383:ℚ)/80109063954218847656250000000000000000000000000000000000000),((8436751923871222550932803:ℚ)/9241600000000000000000000)⟩
theorem valid14 : Valid source25 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source25 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source25 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((368792987:ℚ)/500000000),((3753592521:ℚ)/5000000000),((-9788777563:ℚ)/10537500000),((-2197550909:ℚ)/2646250000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((608669193:ℚ)/2500000000),((381263961479422982587290637938864952004441565472522175259217:ℚ)/1310975234664903808593750000000000000000000000000000000000000),((135204928814636032477147443:ℚ)/147865600000000000000000000)⟩
theorem valid15 : Valid source25 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source25 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((1481123011:ℚ)/2000000000),((7566635211:ℚ)/10000000000),((-19755905633:ℚ)/21170000000),((-8831861077:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((566643037:ℚ)/2500000000),((312746566241286310102266052845440435470289524546806157362667:ℚ)/1056829975179932812500000000000000000000000000000000000000000),((542556992096925429920090283:ℚ)/591462400000000000000000000)⟩
theorem valid16 : Valid source25 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source25 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((746512387:ℚ)/1000000000),((19213829:ℚ)/25000000),((-50281487:ℚ)/53400000),((-4457586709:ℚ)/5435000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((471693769:ℚ)/2500000000),((344000416253941214210019005958839831050219219197895613:ℚ)/1124508847087350000000000000000000000000000000000000000),((941020137:ℚ)/1024000000)⟩
theorem valid17 : Valid source25 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((379206723:ℚ)/500000000),((7804422951:ℚ)/10000000000),((-20469268853:ℚ)/21740000000),((-2270447061:ℚ)/2765000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((323132929:ℚ)/5000000000),((7646421176277422549014254756427531329354450155358735434687:ℚ)/25049140950696875000000000000000000000000000000000000000000),((941020137:ℚ)/1024000000)⟩
theorem valid18 : Valid source25 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((1925784017:ℚ)/2500000000),((8042191543:ℚ)/10000000000),((-21182574629:ℚ)/22120000000),((-11560488119:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((64018897380185733588597361360072714443120863822137841290633:ℚ)/197610228415600000000000000000000000000000000000000000000000),((941020137:ℚ)/1024000000)⟩
theorem valid19 : Valid source25 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((992639267:ℚ)/1250000000),((4496554091:ℚ)/5000000000),(-1:ℚ),((-5988474869:ℚ)/8100000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((7999944622002743734940208375195331:ℚ)/20503125000000000000000000000000000),((941020137:ℚ)/1024000000)⟩
theorem valid20 : Valid source25 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((8892745357:ℚ)/10000000000),((2178883689:ℚ)/2000000000),(-1:ℚ),((-54569217499:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((206225129624044378189259601998137679:ℚ)/500000000000000000000000000000000000),((941020137:ℚ)/1024000000)⟩
theorem valid21 : Valid source25 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((2698769081:ℚ)/2500000000),((3673988983:ℚ)/2500000000),(-1:ℚ),((-16971383567:ℚ)/27600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((10753967053277238387896461:ℚ)/23805000000000000000000000),((941020137:ℚ)/1024000000)⟩
theorem valid22 : Valid source25 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet22 valid22
private theorem node0_2 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source25 nn0 nn1 Qcell ((4063:ℚ)/6400) ((8183:ℚ)/12800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source25 nn0 nn1 Qcell ((1011:ℚ)/1600) ((8183:ℚ)/12800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((8183:ℚ)/12800) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source25 nn0 nn1 Qcell ((4101:ℚ)/6400) ((103:ℚ)/160) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source25 nn0 nn1 Qcell ((8183:ℚ)/12800) ((103:ℚ)/160) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source25 nn0 nn1 Qcell ((8259:ℚ)/12800) ((8297:ℚ)/12800) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((8297:ℚ)/12800) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source25 nn0 nn1 Qcell ((8183:ℚ)/12800) ((8297:ℚ)/12800) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((8297:ℚ)/12800) :=
  cell_join node0_5 node5_11
private theorem node12_14 :
    CellBound source25 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source25 nn0 nn1 Qcell ((8297:ℚ)/12800) ((1049:ℚ)/1600) :=
  cell_join leaf11 node12_14
private theorem node15_17 :
    CellBound source25 nn0 nn1 Qcell ((843:ℚ)/1280) ((267:ℚ)/400) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source25 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf14 node15_17
private theorem node11_17 :
    CellBound source25 nn0 nn1 Qcell ((8297:ℚ)/12800) ((267:ℚ)/400) :=
  cell_join node11_14 node14_17
private theorem node18_20 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf17 node18_20
private theorem node21_23 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf20 node21_23
private theorem node17_23 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node17_20 node20_23
private theorem node11_23 :
    CellBound source25 nn0 nn1 Qcell ((8297:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node11_17 node17_23
private theorem node0_23 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_23
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_23
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22]
theorem packet_count : packets.length = 23 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC02
#check @N11Formalization.C450Source25GroupedC02.bound
#print axioms N11Formalization.C450Source25GroupedC02.valid0
#print axioms N11Formalization.C450Source25GroupedC02.valid1
#print axioms N11Formalization.C450Source25GroupedC02.valid2
#print axioms N11Formalization.C450Source25GroupedC02.valid3
#print axioms N11Formalization.C450Source25GroupedC02.valid4
#print axioms N11Formalization.C450Source25GroupedC02.valid5
#print axioms N11Formalization.C450Source25GroupedC02.valid6
#print axioms N11Formalization.C450Source25GroupedC02.valid7
#print axioms N11Formalization.C450Source25GroupedC02.valid8
#print axioms N11Formalization.C450Source25GroupedC02.valid9
#print axioms N11Formalization.C450Source25GroupedC02.valid10
#print axioms N11Formalization.C450Source25GroupedC02.valid11
#print axioms N11Formalization.C450Source25GroupedC02.valid12
#print axioms N11Formalization.C450Source25GroupedC02.valid13
#print axioms N11Formalization.C450Source25GroupedC02.valid14
#print axioms N11Formalization.C450Source25GroupedC02.valid15
#print axioms N11Formalization.C450Source25GroupedC02.valid16
#print axioms N11Formalization.C450Source25GroupedC02.valid17
#print axioms N11Formalization.C450Source25GroupedC02.valid18
#print axioms N11Formalization.C450Source25GroupedC02.valid19
#print axioms N11Formalization.C450Source25GroupedC02.valid20
#print axioms N11Formalization.C450Source25GroupedC02.valid21
#print axioms N11Formalization.C450Source25GroupedC02.valid22
#print axioms N11Formalization.C450Source25GroupedC02.bound
#print axioms N11Formalization.C450Source25GroupedC02.endpoint_checks
