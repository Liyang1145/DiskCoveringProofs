import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((13:ℚ)/16),((7:ℚ)/8),((523291429:ℚ)/1000000000),((5563886899:ℚ)/10000000000),((8466788577:ℚ)/10300000000),((47587208293:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((8113205787:ℚ)/10000000000),((-2697324276547092446209221743469927207:ℚ)/6829543750000000000000000000000000000),((-6005796454032512395799362389:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((1094246371:ℚ)/2000000000),((725301159:ℚ)/1250000000),((17553202823:ℚ)/21360000000),((6157108113:ℚ)/6437500000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((767139639:ℚ)/1000000000),((-93872661407342940949114399540356339278382217436710853:ℚ)/237927037500000000000000000000000000000000000000000000),((-91925936730003427958832509:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((2854745481:ℚ)/5000000000),((185051359:ℚ)/312500000),((45431691253:ℚ)/54350000000),((1565359513:ℚ)/1668750000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1802110493:ℚ)/2500000000),((-1234022889309514998373785770321142265139725948259637301621:ℚ)/3010231647656250000000000000000000000000000000000000000000),((-5685212402427900653952909:ℚ)/14440000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((2914300261:ℚ)/5000000000),((6040860969:ℚ)/10000000000),((46205903393:ℚ)/55300000000),((50926026783:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1741916803:ℚ)/2500000000),((-81134782459789478925221677940993558788053667267121519489:ℚ)/198178566796875000000000000000000000000000000000000000000),((-15955212584608921976691989:ℚ)/40960000000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((5947697673:ℚ)/10000000000),((6100463703:ℚ)/10000000000),((93960069749:ℚ)/111550000000),((51343245921:ℚ)/55300000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1679945097:ℚ)/2500000000),((-3615308645789389048401729258079944090533980621017706311071:ℚ)/8675384680468750000000000000000000000000000000000000000000),((-15869349072166634592888341:ℚ)/40960000000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((13:ℚ)/16),((7:ℚ)/8),((1201448359:ℚ)/2000000000),((6160062569:ℚ)/10000000000),((18946828667:ℚ)/22500000000),((51760437983:ℚ)/55775000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3296456477:ℚ)/5000000000),((-29643640931858485050164143165549740536632426361879221913:ℚ)/71191406250000000000000000000000000000000000000000000000),((-5697782331893165190534419229:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((6066783049:ℚ)/10000000000),((1243931533:ℚ)/2000000000),((95508179637:ℚ)/113450000000),((10435520731:ℚ)/11250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6463939881:ℚ)/10000000000),((-3797110391847049980966749282434166773673234112908223417327:ℚ)/9126274303906250000000000000000000000000000000000000000000),((-226666946145959655762782421:ℚ)/591462400000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((6126321507:ℚ)/10000000000),((3139624543:ℚ)/5000000000),((7406321507:ℚ)/8800000000),((26297371801:ℚ)/28362500000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1583182407:ℚ)/2500000000),((-6439007479278288984825213918207065397346871832918427:ℚ)/15488000000000000000000000000000000000000000000000000),((-3902707023261922077229701:ℚ)/10240000000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((13:ℚ)/16),((7:ℚ)/8),((6185857239:ℚ)/10000000000),((3154521723:ℚ)/5000000000),((97056144107:ℚ)/114875000000),((26401652061:ℚ)/28600000000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((774892153:ℚ)/1250000000),((-2979144403309141101778589808129955570778179804197433767899:ℚ)/7105879751586914062500000000000000000000000000000000000000),((-1404976390439203980036821381:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((776953013:ℚ)/1250000000),((3169418461:ℚ)/5000000000),((4060129723:ℚ)/4806250000),((26505929227:ℚ)/28718750000),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1226279651:ℚ)/2000000000),((-72699415387430309347123543176656073762698067515906993:ℚ)/173475879287719726562500000000000000000000000000000000),((-1401072039809842461630058869:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2307:ℚ)/3200),((4633:ℚ)/6400),((13:ℚ)/16),((7:ℚ)/8),((6245390313:ℚ)/10000000000),((1592157381:ℚ)/2500000000),((97830074069:ℚ)/115825000000),((4435033889:ℚ)/4806250000),((1905827251:ℚ)/2000000000),((1907725537:ℚ)/2000000000),((3080928657:ℚ)/10000000000),((6063002263:ℚ)/10000000000),((-162726774400211000464437682592955205735741736536482572999:ℚ)/388460563035156250000000000000000000000000000000000000000),((-349291045629880339513165829:ℚ)/924160000000000000000000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4633:ℚ)/6400),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((3137577937:ℚ)/5000000000),((6398421263:ℚ)/10000000000),((49108513181:ℚ)/58150000000),((53428948841:ℚ)/57912500000),((9519843613:ℚ)/10000000000),((476456813:ℚ)/500000000),((622285377:ℚ)/2000000000),((5993926393:ℚ)/10000000000),((-1286481753941075528012621716532532005122680882094698151:ℚ)/3072339349609375000000000000000000000000000000000000000),((-5573011269768281848414394541:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1163:ℚ)/1600),((4671:ℚ)/6400),((13:ℚ)/16),((7:ℚ)/8),((3152460397:ℚ)/5000000000),((128564243:ℚ)/200000000),((49301985161:ℚ)/58387500000),((1072749701:ℚ)/1163000000),((148605427:ℚ)/156250000),((4759921809:ℚ)/5000000000),((98156347:ℚ)/312500000),((2962073247:ℚ)/5000000000),((-390534866712296324105210330682693305043279136436593701377:ℚ)/933041415811157226562500000000000000000000000000000000000),((-2222940709513540074195861:ℚ)/5914624000000000000000000)⟩
theorem valid12 : Valid source28 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((4671:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4671:ℚ)/6400),((469:ℚ)/640),((13:ℚ)/16),((7:ℚ)/8),((6334685083:ℚ)/10000000000),((3229001097:ℚ)/5000000000),((98990906079:ℚ)/117250000000),((8974335893:ℚ)/9731250000),((9501845013:ℚ)/10000000000),((9510747333:ℚ)/10000000000),((792422551:ℚ)/2500000000),((1170727403:ℚ)/2000000000),((-4215061874877627872214459957500546974654946627376501448149:ℚ)/10074385644531250000000000000000000000000000000000000000000),((-1385419559657501949405367901:ℚ)/3696640000000000000000000000)⟩
theorem valid13 : Valid source28 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source28 nn0 nn1 Qcell ((4671:ℚ)/6400) ((469:ℚ)/640) :=
  cell_of_packet source28 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6364448747:ℚ)/10000000000),((3258789899:ℚ)/5000000000),((99377833711:ℚ)/118200000000),((27131529293:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5782370899:ℚ)/10000000000),((-356539129338704465774115388105644224552648150959995868903:ℚ)/860104462500000000000000000000000000000000000000000000000),((-1377572258000285907349228389:ℚ)/3696640000000000000000000000)⟩
theorem valid14 : Valid source28 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source28 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((6423974231:ℚ)/10000000000),((1315430831:ℚ)/2000000000),((100151665003:ℚ)/119150000000),((10936015817:ℚ)/11820000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((112749043:ℚ)/200000000),((-13138344470603000964815020431257036135662844433223333999651:ℚ)/31716365360156250000000000000000000000000000000000000000000),((-219153744692796570753720429:ℚ)/591462400000000000000000000)⟩
theorem valid15 : Valid source28 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((3241748653:ℚ)/5000000000),((3318362671:ℚ)/5000000000),((50462732489:ℚ)/60050000000),((27548538697:ℚ)/29787500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1097827643:ℚ)/2000000000),((-35015826413851009971066886752415972162590987922088867379:ℚ)/84586113330078125000000000000000000000000000000000000000),((-1361835490825200026797187949:ℚ)/3696640000000000000000000000)⟩
theorem valid16 : Valid source28 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source28 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((654301803:ℚ)/1000000000),((1339258687:ℚ)/2000000000),((10169923439:ℚ)/12105000000),((11102810809:ℚ)/12010000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((2668571459:ℚ)/5000000000),((-509579481418249044933485074156893337116087170121902941:ℚ)/1231776428906250000000000000000000000000000000000000000),((-216631361555545200676737741:ℚ)/591462400000000000000000000)⟩
theorem valid17 : Valid source28 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source28 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((6602536459:ℚ)/10000000000),((6755858507:ℚ)/10000000000),((102472973967:ℚ)/122000000000),((55931009549:ℚ)/60525000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2590569541:ℚ)/5000000000),((-4692029725051689010801649478804007476948204292618428386613:ℚ)/11349050000000000000000000000000000000000000000000000000000),((-5384169814325954993674629861:ℚ)/14786560000000000000000000000)⟩
theorem valid18 : Valid source28 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source28 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source28 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((3331026323:ℚ)/5000000000),((859372483:ℚ)/1250000000),((17207780733:ℚ)/20650000000),((7095607381:ℚ)/7625000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((5020749813:ℚ)/10000000000),((-5589860726457643630699696822048646476597966975820308527:ℚ)/13758788476562500000000000000000000000000000000000000000),((-83137068012949822279495221:ℚ)/231040000000000000000000000)⟩
theorem valid19 : Valid source28 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((3390539251:ℚ)/5000000000),((6994089953:ℚ)/10000000000),((52397010263:ℚ)/62900000000),((57598629671:ℚ)/61950000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1171246917:ℚ)/2500000000),((-616537361365296060444272516569333806653584988491527973:ℚ)/1518909844970703125000000000000000000000000000000000000),((-5257149358703382668488921101:ℚ)/14786560000000000000000000000)⟩
theorem valid20 : Valid source28 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source28 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((3450047999:ℚ)/5000000000),((7232278319:ℚ)/10000000000),((17723541329:ℚ)/21600000000),((3486232249:ℚ)/3700000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((4325318859:ℚ)/10000000000),((-916190730093173288945874049481849802294687308039212273:ℚ)/2332800000000000000000000000000000000000000000000000000),((-5129225961674661054017573229:ℚ)/14786560000000000000000000000)⟩
theorem valid21 : Valid source28 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source28 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((7138107383:ℚ)/10000000000),((2284151083:ℚ)/2500000000),((109435395979:ℚ)/160000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((140172611:ℚ)/400000000),((-1262640601009109136241120450458463405575389306798003892643:ℚ)/4800000000000000000000000000000000000000000000000000000000),((-341406951:ℚ)/1024000000)⟩
theorem valid22 : Valid source28 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((9041321893:ℚ)/10000000000),((2588335127:ℚ)/2000000000),((44725728203:ℚ)/73600000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-18952421465807360401614017892398321739:ℚ)/99672064000000000000000000000000000000),((-341406951:ℚ)/1024000000)⟩
theorem valid23 : Valid source28 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet23 valid23
private theorem node1_3 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source28 nn0 nn1 Qcell ((2269:ℚ)/3200) ((919:ℚ)/1280) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((919:ℚ)/1280) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source28 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source28 nn0 nn1 Qcell ((919:ℚ)/1280) ((1163:ℚ)/1600) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_6 node6_12
private theorem node13_15 :
    CellBound source28 nn0 nn1 Qcell ((4671:ℚ)/6400) ((591:ℚ)/800) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf12 node13_15
private theorem node16_18 :
    CellBound source28 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((2421:ℚ)/3200) :=
  cell_join leaf15 node16_18
private theorem node12_18 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_join node12_15 node15_18
private theorem node19_21 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source28 nn0 nn1 Qcell ((2421:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join leaf18 node19_21
private theorem node22_24 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf22 leaf23
private theorem node21_24 :
    CellBound source28 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf21 node22_24
private theorem node18_24 :
    CellBound source28 nn0 nn1 Qcell ((2421:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node18_21 node21_24
private theorem node12_24 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_18 node18_24
private theorem node0_24 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_12 node12_24
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_24
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23]
theorem packet_count : packets.length = 24 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC30
#check @N11Formalization.C450Source28GroupedC30.bound
#print axioms N11Formalization.C450Source28GroupedC30.valid0
#print axioms N11Formalization.C450Source28GroupedC30.valid1
#print axioms N11Formalization.C450Source28GroupedC30.valid2
#print axioms N11Formalization.C450Source28GroupedC30.valid3
#print axioms N11Formalization.C450Source28GroupedC30.valid4
#print axioms N11Formalization.C450Source28GroupedC30.valid5
#print axioms N11Formalization.C450Source28GroupedC30.valid6
#print axioms N11Formalization.C450Source28GroupedC30.valid7
#print axioms N11Formalization.C450Source28GroupedC30.valid8
#print axioms N11Formalization.C450Source28GroupedC30.valid9
#print axioms N11Formalization.C450Source28GroupedC30.valid10
#print axioms N11Formalization.C450Source28GroupedC30.valid11
#print axioms N11Formalization.C450Source28GroupedC30.valid12
#print axioms N11Formalization.C450Source28GroupedC30.valid13
#print axioms N11Formalization.C450Source28GroupedC30.valid14
#print axioms N11Formalization.C450Source28GroupedC30.valid15
#print axioms N11Formalization.C450Source28GroupedC30.valid16
#print axioms N11Formalization.C450Source28GroupedC30.valid17
#print axioms N11Formalization.C450Source28GroupedC30.valid18
#print axioms N11Formalization.C450Source28GroupedC30.valid19
#print axioms N11Formalization.C450Source28GroupedC30.valid20
#print axioms N11Formalization.C450Source28GroupedC30.valid21
#print axioms N11Formalization.C450Source28GroupedC30.valid22
#print axioms N11Formalization.C450Source28GroupedC30.valid23
#print axioms N11Formalization.C450Source28GroupedC30.bound
#print axioms N11Formalization.C450Source28GroupedC30.endpoint_checks
