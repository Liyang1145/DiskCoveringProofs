import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((6441985953:ℚ)/10000000000),((6732060811:ℚ)/10000000000),((-605038143:ℚ)/800000000),((-64461845483:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((34955897:ℚ)/62500000),((1292140348058063936981068742265836890084824925569624623:ℚ)/33948800000000000000000000000000000000000000000000000000),((1666480074048663640729571747:ℚ)/7393280000000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((1335937911:ℚ)/2000000000),((685090941:ℚ)/1000000000),((-1911272823:ℚ)/2575000000),((-13415317021:ℚ)/20980000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((994462859:ℚ)/2000000000),((1058618025235601340219679310464949281306690178373401176223:ℚ)/29356393640795898437500000000000000000000000000000000000000),((50038012263491364895694201:ℚ)/221798400000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((6798535817:ℚ)/10000000000),((54451207:ℚ)/78125000),((-304207242:ℚ)/409765625),((-22794631329:ℚ)/35600000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((463385931:ℚ)/1000000000),((251516352359398469041577929097678286184271873551293607241:ℚ)/6975840653022003173828125000000000000000000000000000000000),((282248839186868966563:ℚ)/1250000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/4),((-11:ℚ)/16),((6917378651:ℚ)/10000000000),((351458789:ℚ)/500000000),((-327458789:ℚ)/445000000),((-69691165161:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((42707453:ℚ)/100000000),((42125140272521035178808266949875557368090790955932727:ℚ)/1198935666586303710937500000000000000000000000000000000),((11565996518613093367627:ℚ)/51200000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((3488399419:ℚ)/5000000000),((3544298127:ℚ)/5000000000),((-9912894381:ℚ)/13468750000),((-35172393609:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4077891479:ℚ)/10000000000),((634091922508048832320572301367050127840451753235351406086429:ℚ)/18043508188796806335449218750000000000000000000000000000000000),((1253149592948445124483622609:ℚ)/5544960000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((1407243647:ℚ)/2000000000),((3559153097:ℚ)/5000000000),((-9957459291:ℚ)/13587500000),((-14199680117:ℚ)/21835000000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((969004357:ℚ)/2500000000),((648446535671153141057771884242456453175657337621466878308059:ℚ)/18687236839326146697998046875000000000000000000000000000000000),((417808755038390750297693163:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((1766481911:ℚ)/2500000000),((7148015939:ℚ)/10000000000),((-20004047817:ℚ)/27293750000),((-5943767007:ℚ)/9137500000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((117851453:ℚ)/312500000),((589173841239394059013154798485219677917362695251229757597033:ℚ)/16976353411152474594116210937500000000000000000000000000000000),((1671604438332908198415889747:ℚ)/7393280000000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-3:ℚ)/4),((-11:ℚ)/16),((3547818431:ℚ)/5000000000),((1794431373:ℚ)/2500000000),((-1674431373:ℚ)/2284375000),((-35826002741:ℚ)/55062500000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((1831814199:ℚ)/5000000000),((501811847211337396290570180888501317877259051063719210493:ℚ)/14456862110922384262084960937500000000000000000000000000000),((313495195968066125436419609:ℚ)/1386240000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((7125345893:ℚ)/10000000000),((900929357:ℚ)/1250000000),((-2522788071:ℚ)/3441406250),((-71978804823:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3552903911:ℚ)/10000000000),((173081508456061637468649630787001890715357362147609032519901:ℚ)/4985607480010247230529785156250000000000000000000000000000000),((26130388135486956079835443:ℚ)/115520000000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7155054739:ℚ)/10000000000),((226160751:ℚ)/312500000),((-633482253:ℚ)/864062500),((-72305602129:ℚ)/111075000000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((1719386233:ℚ)/5000000000),((690882762758849895251613994816745369669216258176122686143:ℚ)/19897940343391138315200805664062500000000000000000000000000),((4900534643144045983855121:ℚ)/21660000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7184763401:ℚ)/10000000000),((7266853023:ℚ)/10000000000),((-6786853023:ℚ)/9256250000),((-72632397411:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3320882289:ℚ)/10000000000),((53545409173537074871277988570383380301744768672833735177583:ℚ)/1541929093358554935455322265625000000000000000000000000000000),((5019261993269840362922201009:ℚ)/22179840000000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((1803617971:ℚ)/2500000000),((7296561833:ℚ)/10000000000),((-20449685499:ℚ)/27887500000),((-18239797681:ℚ)/28006250000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((799704317:ℚ)/2500000000),((3781256032283808528887224111704266354844862595116177006147051:ℚ)/108872613008126050292968750000000000000000000000000000000000000),((1673459359401832235097268523:ℚ)/7393280000000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-3:ℚ)/4),((-11:ℚ)/16),((1811045047:ℚ)/2500000000),((7326270461:ℚ)/10000000000),((-20538811383:ℚ)/28006250000),((-18321495517:ℚ)/28125000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((3072079241:ℚ)/10000000000),((1508915841987401795054953858629124403673704578691465107:ℚ)/43440013813501596450805664062500000000000000000000000000),((1673831909773358099318555347:ℚ)/7393280000000000000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7273888317:ℚ)/10000000000),((7355978913:ℚ)/10000000000),((-2291992971:ℚ)/3125000000),((-73612771487:ℚ)/112975000000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((2940063349:ℚ)/10000000000),((135314865497176800662620460437324442184571694645448629645899:ℚ)/3895065498352050781250000000000000000000000000000000000000000),((5022614946810862612438028849:ℚ)/22179840000000000000000000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((456474767:ℚ)/625000000),((1846421797:ℚ)/2500000000),((-5179265391:ℚ)/7060937500),((-4621222437:ℚ)/7090625000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((280202309:ℚ)/1000000000),((983921913764503397098408673824702029583361447956799692979:ℚ)/28318883041095232903957366943359375000000000000000000000000),((104661161054419843715677763:ℚ)/462080000000000000000000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((1466660811:ℚ)/2000000000),((7445103221:ℚ)/10000000000),((-20895309663:ℚ)/28362500000),((-14853268921:ℚ)/22880000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2657019031:ℚ)/10000000000),((102562907300825012347585115063690207618592694043172152630603:ℚ)/2915987238134045410156250000000000000000000000000000000000000),((1675327332521266197892295587:ℚ)/7393280000000000000000000000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((1848179779:ℚ)/2500000000),((7563933273:ℚ)/10000000000),((-21251799819:ℚ)/28600000000),((-18729977569:ℚ)/29075000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2340883891:ℚ)/10000000000),((647392496108934982528898717077581649407759451845529075153569:ℚ)/17978144262650000000000000000000000000000000000000000000000000),((5030493330152705743218935009:ℚ)/22179840000000000000000000000)⟩
theorem valid16 : Valid source11 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((938943409:ℚ)/1250000000),((30731043:ℚ)/40000000),((-86433129:ℚ)/116300000),((-3176125833:ℚ)/4925000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1527164893:ℚ)/10000000000),((3433740777289176751581146783194555947538673275699881:ℚ)/95387534255192187500000000000000000000000000000000000),((116155761:ℚ)/512000000)⟩
theorem valid17 : Valid source11 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/4),((-11:ℚ)/16),((3815186457:ℚ)/5000000000),((990051057:ℚ)/1250000000),((-930051057:ℚ)/1231250000),((-38767051027:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((1630791915675679407452589329826418427640220078200122073:ℚ)/43408863728332519531250000000000000000000000000000000000),((116155761:ℚ)/512000000)⟩
theorem valid18 : Valid source11 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((3934008561:ℚ)/5000000000),((4197838931:ℚ)/5000000000),((-11873516793:ℚ)/15250000000),((-40074094171:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((5886175017362461138550163732090381277172820727922142546337:ℚ)/145431869238281250000000000000000000000000000000000000000000),((116155761:ℚ)/512000000)⟩
theorem valid19 : Valid source11 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((2085820037:ℚ)/2500000000),((1029649939:ℚ)/1000000000),((-981649939:ℚ)/1080000000),((-21344020407:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((83352044376306332145954039780441609503898352568017:ℚ)/1476225000000000000000000000000000000000000000000000),((116155761:ℚ)/512000000)⟩
theorem valid20 : Valid source11 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((5122041113:ℚ)/5000000000),((7048731769:ℚ)/5000000000),(-1:ℚ),((-53142452243:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((107757781856092711066240651:ℚ)/1523520000000000000000000000),((116155761:ℚ)/512000000)⟩
theorem valid21 : Valid source11 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet21 valid21
private theorem node0_2 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source11 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source11 nn0 nn1 Qcell ((4367:ℚ)/6400) ((881:ℚ)/1280) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((881:ℚ)/1280) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source11 nn0 nn1 Qcell ((881:ℚ)/1280) ((2231:ℚ)/3200) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_5 node5_11
private theorem node11_13 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf11 leaf12
private theorem node14_16 :
    CellBound source11 nn0 nn1 Qcell ((4519:ℚ)/6400) ((143:ℚ)/200) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf13 node14_16
private theorem node11_16 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join node11_13 node13_16
private theorem node17_19 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf16 node17_19
private theorem node20_22 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf19 node20_22
private theorem node16_22 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node16_19 node19_22
private theorem node11_22 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node11_16 node16_22
private theorem node0_22 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_22
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_22
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21]
theorem packet_count : packets.length = 22 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC05
#check @N11Formalization.C450Source11GroupedC05.bound
#print axioms N11Formalization.C450Source11GroupedC05.valid0
#print axioms N11Formalization.C450Source11GroupedC05.valid1
#print axioms N11Formalization.C450Source11GroupedC05.valid2
#print axioms N11Formalization.C450Source11GroupedC05.valid3
#print axioms N11Formalization.C450Source11GroupedC05.valid4
#print axioms N11Formalization.C450Source11GroupedC05.valid5
#print axioms N11Formalization.C450Source11GroupedC05.valid6
#print axioms N11Formalization.C450Source11GroupedC05.valid7
#print axioms N11Formalization.C450Source11GroupedC05.valid8
#print axioms N11Formalization.C450Source11GroupedC05.valid9
#print axioms N11Formalization.C450Source11GroupedC05.valid10
#print axioms N11Formalization.C450Source11GroupedC05.valid11
#print axioms N11Formalization.C450Source11GroupedC05.valid12
#print axioms N11Formalization.C450Source11GroupedC05.valid13
#print axioms N11Formalization.C450Source11GroupedC05.valid14
#print axioms N11Formalization.C450Source11GroupedC05.valid15
#print axioms N11Formalization.C450Source11GroupedC05.valid16
#print axioms N11Formalization.C450Source11GroupedC05.valid17
#print axioms N11Formalization.C450Source11GroupedC05.valid18
#print axioms N11Formalization.C450Source11GroupedC05.valid19
#print axioms N11Formalization.C450Source11GroupedC05.valid20
#print axioms N11Formalization.C450Source11GroupedC05.valid21
#print axioms N11Formalization.C450Source11GroupedC05.bound
#print axioms N11Formalization.C450Source11GroupedC05.endpoint_checks
