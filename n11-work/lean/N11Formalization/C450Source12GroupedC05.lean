import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((404261989:ℚ)/625000000),((6760917997:ℚ)/10000000000),((-18682753991:ℚ)/24800000000),((-4006881879:ℚ)/6437500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((276380751:ℚ)/500000000),((2482641419110903414115961283238409008415223665986734324697:ℚ)/63210543800000000000000000000000000000000000000000000000000),((746629184547418410173081803:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((335297163:ℚ)/500000000),((1719946833:ℚ)/2500000000),((-4759840499:ℚ)/6437500000),((-3336268793:ℚ)/5245000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4899402963:ℚ)/10000000000),((1066146157521193586556203175336361864314546508732112841053:ℚ)/28668353164839744567871093750000000000000000000000000000000),((140095251353467988165571289:ℚ)/554496000000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((6824812137:ℚ)/10000000000),((6939220391:ℚ)/10000000000),((-19217661173:ℚ)/26225000000),((-68032933507:ℚ)/105850000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4555899823:ℚ)/10000000000),((15661131307066963213732806605966668714625579649021990360563:ℚ)/432539108911480712890625000000000000000000000000000000000000),((747448020860183778693817827:ℚ)/2957312000000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((6884244973:ℚ)/10000000000),((1399730483:ℚ)/2000000000),((-3879191449:ℚ)/5292500000),((-22895564901:ℚ)/35600000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((4374810619:ℚ)/10000000000),((113784348421673907614526217258654480582828517418945923:ℚ)/3141736750796508789062500000000000000000000000000000000),((29908870780615664255031563:ℚ)/118292480000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/4),((-11:ℚ)/16),((3471838389:ℚ)/5000000000),((882260429:ℚ)/1250000000),((-2446781287:ℚ)/3337500000),((-34670222279:ℚ)/53875000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((418642383:ℚ)/1000000000),((63621901940496801699702297629404392502099886766360559:ℚ)/1756253417851030826568603515625000000000000000000000000),((11687436249356397370913547:ℚ)/46208000000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((350155379:ℚ)/500000000),((1771949643:ℚ)/2500000000),((-4915848929:ℚ)/6734375000),((-1166569723:ℚ)/1803750000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((249356383:ℚ)/625000000),((185069634599092068638089931129042824705373008592145471929:ℚ)/5175393166230339556932449340820312500000000000000000000000),((140274964853774311385524849:ℚ)/554496000000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((7032822613:ℚ)/10000000000),((7117513469:ℚ)/10000000000),((-19752540407:ℚ)/27056250000),((-70321048743:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((777564247:ℚ)/2000000000),((327287551196716674467819337291745672735157239849384318829:ℚ)/9150744808059597015380859375000000000000000000000000000000),((748270472294603699908694187:ℚ)/2957312000000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((1412507481:ℚ)/2000000000),((223350879:ℚ)/312500000),((-620052637:ℚ)/849218750),((-1284507481:ℚ)/1985000000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((756668339:ℚ)/2000000000),((5395250909267814922697025034325831324022428806888327879:ℚ)/150820286990945786237716674804687500000000000000000000000),((2192601267195913827909241:ℚ)/8664000000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((177306299:ℚ)/250000000),((7176942551:ℚ)/10000000000),((-1811893423:ℚ)/2481250000),((-1774369289:ℚ)/2741250000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((735208289:ℚ)/2000000000),((85564970904534283146750981443203861350504310249192294883:ℚ)/2391484796837782859802246093750000000000000000000000000000),((748545426618419717591440067:ℚ)/2957312000000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-3:ℚ)/4),((-11:ℚ)/16),((7121966279:ℚ)/10000000000),((3603328371:ℚ)/5000000000),((-10009985113:ℚ)/13706250000),((-71301629069:ℚ)/110125000000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((3565665349:ℚ)/10000000000),((258670332696982040725053323831510262568276017561964202997:ℚ)/7228431055461192131042480468750000000000000000000000000000),((561512290918020047467950241:ℚ)/2217984000000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((7151680367:ℚ)/10000000000),((7236370703:ℚ)/10000000000),((-20109112109:ℚ)/27531250000),((-71628484037:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1725958921:ℚ)/5000000000),((25491450744816144092501469414832597857049594253137064021893:ℚ)/712229640001463890075683593750000000000000000000000000000000),((748820783026586946489729203:ℚ)/2957312000000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7181394227:ℚ)/10000000000),((7266084437:ℚ)/10000000000),((-20198253311:ℚ)/27650000000),((-71955336497:ℚ)/111075000000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3334453383:ℚ)/10000000000),((486251588743201209975218984139072924668299896136381138800659:ℚ)/13583660607755017089843750000000000000000000000000000000000000),((748958612037661999872152123:ℚ)/2957312000000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((360555393:ℚ)/500000000),((1823949487:ℚ)/2500000000),((-5071848461:ℚ)/6942187500),((-37258859:ℚ)/57500000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1606431887:ℚ)/5000000000),((45837686098153830221827699315224214478386430602358607:ℚ)/1280297698146849870681762695312500000000000000000000000),((46818533850426974630177523:ℚ)/184832000000000000000000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7240821271:ℚ)/10000000000),((3662755619:ℚ)/5000000000),((-10188266857:ℚ)/13943750000),((-72609033981:ℚ)/112025000000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((154333049:ℚ)/500000000),((30456903800062440285611643600028197941441229837879237227791:ℚ)/850567289125984767913818359375000000000000000000000000000000),((187308642935275650461220587:ℚ)/739328000000000000000000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-3:ℚ)/4),((-11:ℚ)/16),((3635267231:ℚ)/5000000000),((7355224309:ℚ)/10000000000),((-20465672927:ℚ)/28006250000),((-12155979847:ℚ)/18750000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((2955253461:ℚ)/10000000000),((57619103417400002170961559147474930920819211549345727:ℚ)/1608889400500059127807617187500000000000000000000000000),((749372702447509265075916027:ℚ)/2957312000000000000000000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((1460049487:ℚ)/2000000000),((741464981:ℚ)/1000000000),((-2064394943:ℚ)/2812500000),((-14652544357:ℚ)/22690000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((2817912563:ℚ)/10000000000),((450718246198595449333079570642222411391041477269272101:ℚ)/12428082257509231567382812500000000000000000000000000000),((7496492656422623047212987:ℚ)/29573120000000000000000000)⟩
theorem valid15 : Valid source12 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((3679836371:ℚ)/5000000000),((747407447:ℚ)/1000000000),((-2082222341:ℚ)/2836250000),((-3359836371:ℚ)/5200000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2521510899:ℚ)/10000000000),((437046074091417902738768810708785540816207358858234221:ℚ)/12049534041876220703125000000000000000000000000000000000),((7499262312620687357630403:ℚ)/29573120000000000000000000)⟩
theorem valid16 : Valid source12 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((7419097211:ℚ)/10000000000),((3796460677:ℚ)/5000000000),((-10589382031:ℚ)/14300000000),((-74570069321:ℚ)/116300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((273278893:ℚ)/1250000000),((5217402525870849466380087895091304720761879351467232503403:ℚ)/140454252051953125000000000000000000000000000000000000000000),((187620342528702536272961243:ℚ)/739328000000000000000000000)⟩
theorem valid17 : Valid source12 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((7537943723:ℚ)/10000000000),((12049633:ℚ)/15625000),((-67297798:ℚ)/90859375),((-75877380953:ℚ)/118200000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((639391739:ℚ)/5000000000),((1729605961651177928764236748004334714718183443542792731:ℚ)/46575944460543060302734375000000000000000000000000000000),((259873437:ℚ)/1024000000)⟩
theorem valid18 : Valid source12 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/4),((-11:ℚ)/16),((7656787129:ℚ)/10000000000),((198736097:ℚ)/250000000),((-556208291:ℚ)/738750000),((-77184658419:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((60598800606130924185263407297882356693114936505886183:ℚ)/1562719094219970703125000000000000000000000000000000000),((259873437:ℚ)/1024000000)⟩
theorem valid19 : Valid source12 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((3947232601:ℚ)/5000000000),((8424769919:ℚ)/10000000000),((-23674309757:ℚ)/30500000000),((-39899558611:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((16616539704637036174323903324559307722351205761011378293:ℚ)/397354833984375000000000000000000000000000000000000000000),((259873437:ℚ)/1024000000)⟩
theorem valid20 : Valid source12 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((8369789989:ℚ)/10000000000),((2065152821:ℚ)/2000000000),((-5875458463:ℚ)/6480000000),((-85027689879:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((129713639014590728785875232518265030726497264235547:ℚ)/2214337500000000000000000000000000000000000000000000),((259873437:ℚ)/1024000000)⟩
theorem valid21 : Valid source12 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((10270780357:ℚ)/10000000000),((14126930821:ℚ)/10000000000),(-1:ℚ),((-35312861309:ℚ)/73600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((10004339489423062444772233:ℚ)/135424000000000000000000000),((259873437:ℚ)/1024000000)⟩
theorem valid22 : Valid source12 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet22 valid22
private theorem node0_2 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source12 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source12 nn0 nn1 Qcell ((1049:ℚ)/1600) ((431:ℚ)/640) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source12 nn0 nn1 Qcell ((4329:ℚ)/6400) ((4367:ℚ)/6400) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source12 nn0 nn1 Qcell ((431:ℚ)/640) ((4367:ℚ)/6400) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source12 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source12 nn0 nn1 Qcell ((4367:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source12 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_5 node5_11
private theorem node12_14 :
    CellBound source12 nn0 nn1 Qcell ((4443:ℚ)/6400) ((4481:ℚ)/6400) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((4481:ℚ)/6400) :=
  cell_join leaf11 node12_14
private theorem node15_17 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source12 nn0 nn1 Qcell ((4481:ℚ)/6400) ((143:ℚ)/200) :=
  cell_join leaf14 node15_17
private theorem node11_17 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join node11_14 node14_17
private theorem node18_20 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf17 node18_20
private theorem node21_23 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf20 node21_23
private theorem node17_23 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node17_20 node20_23
private theorem node11_23 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_17 node17_23
private theorem node0_23 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_23
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_23
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22]
theorem packet_count : packets.length = 23 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC05
#check @N11Formalization.C450Source12GroupedC05.bound
#print axioms N11Formalization.C450Source12GroupedC05.valid0
#print axioms N11Formalization.C450Source12GroupedC05.valid1
#print axioms N11Formalization.C450Source12GroupedC05.valid2
#print axioms N11Formalization.C450Source12GroupedC05.valid3
#print axioms N11Formalization.C450Source12GroupedC05.valid4
#print axioms N11Formalization.C450Source12GroupedC05.valid5
#print axioms N11Formalization.C450Source12GroupedC05.valid6
#print axioms N11Formalization.C450Source12GroupedC05.valid7
#print axioms N11Formalization.C450Source12GroupedC05.valid8
#print axioms N11Formalization.C450Source12GroupedC05.valid9
#print axioms N11Formalization.C450Source12GroupedC05.valid10
#print axioms N11Formalization.C450Source12GroupedC05.valid11
#print axioms N11Formalization.C450Source12GroupedC05.valid12
#print axioms N11Formalization.C450Source12GroupedC05.valid13
#print axioms N11Formalization.C450Source12GroupedC05.valid14
#print axioms N11Formalization.C450Source12GroupedC05.valid15
#print axioms N11Formalization.C450Source12GroupedC05.valid16
#print axioms N11Formalization.C450Source12GroupedC05.valid17
#print axioms N11Formalization.C450Source12GroupedC05.valid18
#print axioms N11Formalization.C450Source12GroupedC05.valid19
#print axioms N11Formalization.C450Source12GroupedC05.valid20
#print axioms N11Formalization.C450Source12GroupedC05.valid21
#print axioms N11Formalization.C450Source12GroupedC05.valid22
#print axioms N11Formalization.C450Source12GroupedC05.bound
#print axioms N11Formalization.C450Source12GroupedC05.endpoint_checks
