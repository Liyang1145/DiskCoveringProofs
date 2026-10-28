import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((6869935429:ℚ)/10000000000),((3539375001:ℚ)/5000000000),(-1:ℚ),((-18177806287:ℚ)/20220000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4419043809:ℚ)/10000000000),((16521944631088337431386128152434311:ℚ)/170353500000000000000000000000000000),((8944628544543372816268151:ℚ)/10830000000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((1747195171:ℚ)/2500000000),((3569062501:ℚ)/5000000000),(-1:ℚ),((-4633585513:ℚ)/5102500000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((403795297:ℚ)/1000000000),((453847572570303694892176405571:ℚ)/4814257812500000000000000000000),((2989557753745122833547717:ℚ)/3610000000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((352410099:ℚ)/500000000),((3583906251:ℚ)/5000000000),(-1:ℚ),((-935630297:ℚ)/1025250000),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((59907563:ℚ)/156250000),((54274339165399273902152285661207:ℚ)/583965312500000000000000000000000),((8980707617587347788143151:ℚ)/10830000000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4101:ℚ)/6400),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((3538956153:ℚ)/5000000000),((3598750001:ℚ)/5000000000),(-1:ℚ),((-9400868459:ℚ)/10300000000),((9864186891:ℚ)/10000000000),((9880131563:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((3728189941:ℚ)/10000000000),((12314421179680832488770118835381521:ℚ)/132612500000000000000000000000000000),((2997583324203327124172717:ℚ)/3610000000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((4101:ℚ)/6400) ((103:ℚ)/160) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((103:ℚ)/160),((8259:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((3553811211:ℚ)/5000000000),((901542969:ℚ)/1250000000),(-1:ℚ),((-9445433633:ℚ)/10323750000),((9856320801:ℚ)/10000000000),((616511681:ℚ)/625000000),((1697201141:ℚ)/10000000000),((3619348443:ℚ)/10000000000),((4094740936076950880530131609146713:ℚ)/44408255859375000000000000000000000),((562423384351424595377111:ℚ)/676875000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((8259:ℚ)/12800) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((8259:ℚ)/12800),((4139:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7122477401:ℚ)/10000000000),((3613593751:ℚ)/5000000000),(-1:ℚ),((-18935432203:ℚ)/20695000000),((984852489:ℚ)/1000000000),((4928160403:ℚ)/5000000000),((1742751127:ℚ)/10000000000),((1781869079:ℚ)/5000000000),((4934329448406058615831744519160451:ℚ)/53535378125000000000000000000000000),((3001600108767756417922717:ℚ)/3610000000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((8259:ℚ)/12800) ((4139:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4139:ℚ)/6400),((8297:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7137332329:ℚ)/10000000000),((1810507813:ℚ)/2500000000),(-1:ℚ),((-18979996987:ℚ)/20742500000),((9840798677:ℚ)/10000000000),((1969704979:ℚ)/2000000000),((1786759881:ℚ)/10000000000),((876821161:ℚ)/2500000000),((24775109420608646360827703821530519:ℚ)/268907066406250000000000000000000000),((750902375220950712976773:ℚ)/902500000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((4139:ℚ)/6400) ((8297:ℚ)/12800) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((8297:ℚ)/12800),((2079:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((1430437441:ℚ)/2000000000),((3628437501:ℚ)/5000000000),(-1:ℚ),((-3804912323:ℚ)/4158000000),((4916570841:ℚ)/5000000000),((4920399341:ℚ)/5000000000),((1829340989:ℚ)/10000000000),((3449946447:ℚ)/10000000000),((15796083904114585244240524749653:ℚ)/171517500000000000000000000000000),((9016858678667211431893151:ℚ)/10830000000000000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((8297:ℚ)/12800) ((2079:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2079:ℚ)/3200),((1667:ℚ)/2560),(-1:ℚ),((-15:ℚ)/16),((7167042031:ℚ)/10000000000),((227241211:ℚ)/312500000),(-1:ℚ),((-19069126093:ℚ)/20837500000),((4912776717:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((935297099:ℚ)/5000000000),((847919657:ℚ)/2500000000),((49965630763457699965694836846162541:ℚ)/542751757812500000000000000000000000),((11748555799935778492557:ℚ)/14101562500000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1667:ℚ)/2560) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1667:ℚ)/2560),((4177:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((3590948403:ℚ)/5000000000),((3643281251:ℚ)/5000000000),(-1:ℚ),((-9556845209:ℚ)/10442500000),((4909016731:ℚ)/5000000000),((9825553439:ℚ)/10000000000),((382121547:ℚ)/2000000000),((3332432363:ℚ)/10000000000),((12543529559647422369759645493102497:ℚ)/136307257812500000000000000000000000),((3009641676567269302297717:ℚ)/3610000000000000000000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((1667:ℚ)/2560) ((4177:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4177:ℚ)/6400),((8373:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7196751531:ℚ)/10000000000),((1825351563:ℚ)/2500000000),(-1:ℚ),((-19158254593:ℚ)/20932500000),((4905290651:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((194946007:ℚ)/1000000000),((1636077217:ℚ)/5000000000),((50383126660696208470152308625089873:ℚ)/547711945312500000000000000000000000),((2258740301180150376430319:ℚ)/2707500000000000000000000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8373:ℚ)/12800) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8373:ℚ)/12800),((1049:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((3605803103:ℚ)/5000000000),((3658125001:ℚ)/5000000000),(-1:ℚ),((-9601409309:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((9810581307:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((321078667:ℚ)/1000000000),((18972246000202251917741295102249671:ℚ)/206325187500000000000000000000000000),((3013666459802352892922717:ℚ)/3610000000000000000000000)⟩
theorem valid11 : Valid source20 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source20 nn0 nn1 Qcell ((8373:ℚ)/12800) ((1049:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1049:ℚ)/1600),((8411:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((225826901:ℚ)/312500000),((916386719:ℚ)/1250000000),(-1:ℚ),((-601480703:ℚ)/657109375),((9795878581:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((1011977397:ℚ)/5000000000),((314826527:ℚ)/1000000000),((50802706212506654335569013035142671:ℚ)/552694695312500000000000000000000000),((188479990703357904709037:ℚ)/225625000000000000000000)⟩
theorem valid12 : Valid source20 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source20 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8411:ℚ)/12800) :=
  cell_of_packet source20 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((8411:ℚ)/12800),((843:ℚ)/1280),(-1:ℚ),((-15:ℚ)/16),((452582213:ℚ)/625000000),((3672968751:ℚ)/5000000000),(-1:ℚ),((-1205746639:ℚ)/1317187500),((978862711:ℚ)/1000000000),((4897939293:ℚ)/5000000000),((2059717253:ℚ)/10000000000),((1542260009:ℚ)/5000000000),((637665966099838509931333473148267:ℚ)/6939931640625000000000000000000000),((9053081727782963747518151:ℚ)/10830000000000000000000000)⟩
theorem valid13 : Valid source20 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source20 nn0 nn1 Qcell ((8411:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_of_packet source20 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((843:ℚ)/1280),((8449:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((453510621:ℚ)/625000000),((1840195313:ℚ)/2500000000),(-1:ℚ),((-172647409:ℚ)/188593750),((4890720817:ℚ)/5000000000),((1957725423:ℚ)/2000000000),((83782417:ℚ)/400000000),((120778933:ℚ)/400000000),((3136185866565206045641391750181397:ℚ)/34144898437500000000000000000000000),((754927158456034303601773:ℚ)/902500000000000000000000)⟩
theorem valid14 : Valid source20 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source20 nn0 nn1 Qcell ((843:ℚ)/1280) ((8449:ℚ)/12800) :=
  cell_of_packet source20 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((8449:ℚ)/12800),((2117:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((1454204883:ℚ)/2000000000),((3687812501:ℚ)/5000000000),(-1:ℚ),((-3876214649:ℚ)/4234000000),((9774321709:ℚ)/10000000000),((9781441639:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1476519561:ℚ)/5000000000),((2057439272394785780121804981022159:ℚ)/22408445000000000000000000000000000),((3021724024943174371047717:ℚ)/3610000000000000000000000)⟩
theorem valid15 : Valid source20 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source20 nn0 nn1 Qcell ((8449:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((1457175769:ℚ)/2000000000),((3702656251:ℚ)/5000000000),(-1:ℚ),((-3885127307:ℚ)/4253000000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((2885121491:ℚ)/10000000000),((6262994889500602411300190470211047:ℚ)/67830033750000000000000000000000000),((3025756806848912258547717:ℚ)/3610000000000000000000000)⟩
theorem valid16 : Valid source20 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source20 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((1828896891:ℚ)/2500000000),((3717500001:ℚ)/5000000000),(-1:ℚ),((-4878690673:ℚ)/5340000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((1372196347:ℚ)/5000000000),((1644347158910730683735505733707199:ℚ)/17822250000000000000000000000000000),((9089376764934604735018151:ℚ)/10830000000000000000000000)⟩
theorem valid17 : Valid source20 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source20 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),(-1:ℚ),((-15:ℚ)/16),((7345296093:ℚ)/10000000000),((3747187501:ℚ)/5000000000),(-1:ℚ),((-19603888279:ℚ)/21550000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((259624951:ℚ)/1000000000),((5076056880605289859050353002298069:ℚ)/54422167968750000000000000000000000),((3037871149907434514797717:ℚ)/3610000000000000000000000)⟩
theorem valid18 : Valid source20 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source20 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((1480942519:ℚ)/2000000000),((3776875001:ℚ)/5000000000),(-1:ℚ),((-3956427557:ℚ)/4348000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2271850193:ℚ)/10000000000),((2200667800125384600919521982617981:ℚ)/23631380000000000000000000000000000),((3045960709730873180422717:ℚ)/3610000000000000000000000)⟩
theorem valid19 : Valid source20 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source20 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),(-1:ℚ),((-15:ℚ)/16),((746412837:ℚ)/1000000000),((3836250001:ℚ)/5000000000),(-1:ℚ),((-1996038511:ℚ)/2212000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1893746081:ℚ)/10000000000),((31138480034429581522337802392477:ℚ)/327652500000000000000000000000000),((13211:ℚ)/15625)⟩
theorem valid20 : Valid source20 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source20 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((3791478909:ℚ)/5000000000),((3955000001:ℚ)/5000000000),(-1:ℚ),((-10158436727:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((669810561:ℚ)/10000000000),((16121891364928144676362377142554399:ℚ)/163592000000000000000000000000000000),((13211:ℚ)/15625)⟩
theorem valid21 : Valid source20 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((7820608789:ℚ)/10000000000),((4430000001:ℚ)/5000000000),(-1:ℚ),((-21029826367:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((97484779838865669041041945674820781:ℚ)/839808000000000000000000000000000000),((13211:ℚ)/15625)⟩
theorem valid22 : Valid source20 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((877112407:ℚ)/1000000000),((5380000001:ℚ)/5000000000),(-1:ℚ),((-2388137221:ℚ)/3200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((4910933503094081156060871638132053:ℚ)/38400000000000000000000000000000000),((13211:ℚ)/15625)⟩
theorem valid23 : Valid source20 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((2134372151:ℚ)/2000000000),((14560000003:ℚ)/10000000000),(-1:ℚ),((-5916716453:ℚ)/8832000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1440273675132269204441459:ℚ)/9750528000000000000000000),((13211:ℚ)/15625)⟩
theorem valid24 : Valid source20 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet24 valid24
private theorem node1_3 :
    CellBound source20 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4101:ℚ)/6400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((4101:ℚ)/6400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source20 nn0 nn1 Qcell ((4101:ℚ)/6400) ((4139:ℚ)/6400) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((4139:ℚ)/6400) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source20 nn0 nn1 Qcell ((8297:ℚ)/12800) ((1667:ℚ)/2560) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source20 nn0 nn1 Qcell ((4139:ℚ)/6400) ((1667:ℚ)/2560) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source20 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source20 nn0 nn1 Qcell ((1667:ℚ)/2560) ((1049:ℚ)/1600) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source20 nn0 nn1 Qcell ((4139:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_6 node6_12
private theorem node13_15 :
    CellBound source20 nn0 nn1 Qcell ((8411:ℚ)/12800) ((8449:ℚ)/12800) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source20 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8449:ℚ)/12800) :=
  cell_join leaf12 node13_15
private theorem node16_18 :
    CellBound source20 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source20 nn0 nn1 Qcell ((8449:ℚ)/12800) ((267:ℚ)/400) :=
  cell_join leaf15 node16_18
private theorem node12_18 :
    CellBound source20 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join node12_15 node15_18
private theorem node19_21 :
    CellBound source20 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf18 node19_21
private theorem node21_23 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf21 leaf22
private theorem node23_25 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf23 leaf24
private theorem node21_25 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node21_23 node23_25
private theorem node18_25 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node18_21 node21_25
private theorem node12_25 :
    CellBound source20 nn0 nn1 Qcell ((1049:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_18 node18_25
private theorem node0_25 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_12 node12_25
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_25
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24]
theorem packet_count : packets.length = 25 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC01
#check @N11Formalization.C450Source20GroupedC01.bound
#print axioms N11Formalization.C450Source20GroupedC01.valid0
#print axioms N11Formalization.C450Source20GroupedC01.valid1
#print axioms N11Formalization.C450Source20GroupedC01.valid2
#print axioms N11Formalization.C450Source20GroupedC01.valid3
#print axioms N11Formalization.C450Source20GroupedC01.valid4
#print axioms N11Formalization.C450Source20GroupedC01.valid5
#print axioms N11Formalization.C450Source20GroupedC01.valid6
#print axioms N11Formalization.C450Source20GroupedC01.valid7
#print axioms N11Formalization.C450Source20GroupedC01.valid8
#print axioms N11Formalization.C450Source20GroupedC01.valid9
#print axioms N11Formalization.C450Source20GroupedC01.valid10
#print axioms N11Formalization.C450Source20GroupedC01.valid11
#print axioms N11Formalization.C450Source20GroupedC01.valid12
#print axioms N11Formalization.C450Source20GroupedC01.valid13
#print axioms N11Formalization.C450Source20GroupedC01.valid14
#print axioms N11Formalization.C450Source20GroupedC01.valid15
#print axioms N11Formalization.C450Source20GroupedC01.valid16
#print axioms N11Formalization.C450Source20GroupedC01.valid17
#print axioms N11Formalization.C450Source20GroupedC01.valid18
#print axioms N11Formalization.C450Source20GroupedC01.valid19
#print axioms N11Formalization.C450Source20GroupedC01.valid20
#print axioms N11Formalization.C450Source20GroupedC01.valid21
#print axioms N11Formalization.C450Source20GroupedC01.valid22
#print axioms N11Formalization.C450Source20GroupedC01.valid23
#print axioms N11Formalization.C450Source20GroupedC01.valid24
#print axioms N11Formalization.C450Source20GroupedC01.bound
#print axioms N11Formalization.C450Source20GroupedC01.endpoint_checks
