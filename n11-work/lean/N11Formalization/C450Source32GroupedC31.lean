import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((7:ℚ)/8),((15:ℚ)/16),((1004493229:ℚ)/2000000000),((5361232821:ℚ)/10000000000),((8951452603:ℚ)/10300000000),(1:ℚ),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1061055627:ℚ)/1250000000),((-175567512831455031252007409748269323:ℚ)/530450000000000000000000000000000000),((-19356686106174263615618563:ℚ)/36966400000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((5260522067:ℚ)/10000000000),((5599671047:ℚ)/10000000000),((46423654469:ℚ)/53400000000),(1:ℚ),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((8062994649:ℚ)/10000000000),((-792599071871972380358013962640343199:ℚ)/2376300000000000000000000000000000000),((-477176022123907929385703427:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((5498538299:ℚ)/10000000000),((2859432711:ℚ)/5000000000),((48089768093:ℚ)/54350000000),((10562298133:ℚ)/10680000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7619490663:ℚ)/10000000000),((-1883923516745573793213336442908491957044071712790075443768883:ℚ)/5397642466019280000000000000000000000000000000000000000000000),((-473999115861994139315293843:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((2808766419:ℚ)/5000000000),((2919022223:ℚ)/5000000000),((24461364933:ℚ)/27650000000),((10741066669:ℚ)/10870000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3694951153:ℚ)/5000000000),((-4606107484843483169101564634958924413628578667853772159237:ℚ)/13150798999115859375000000000000000000000000000000000000000),((-352982999657761678183980169:ℚ)/693120000000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((5736518949:ℚ)/10000000000),((184300889:ℚ)/312500000),((49755632643:ℚ)/55775000000),((96700381:ℚ)/98750000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((7154393471:ℚ)/10000000000),((-2151976100471550455707067284067264327682459300059334753:ℚ)/5991291723825683593750000000000000000000000000000000000),((-1407198363206437160011646329:ℚ)/2772480000000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((7:ℚ)/8),((15:ℚ)/16),((289800449:ℚ)/500000000),((2978604451:ℚ)/5000000000),((2508603143:ℚ)/2812500000),((10919813353:ℚ)/11155000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1758556701:ℚ)/2500000000),((-244161922786691382096264892149710714203635029723302787:ℚ)/678943148906250000000000000000000000000000000000000000),((-1168480990204547247006443:ℚ)/2310400000000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((5855497063:ℚ)/10000000000),((3008392949:ℚ)/5000000000),((50588479441:ℚ)/56725000000),((11009178847:ℚ)/11250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1382467377:ℚ)/2000000000),((-3299035932255194675086943736080224853248418323958032018264939:ℚ)/9162976486816406250000000000000000000000000000000000000000000),((-465719792132784120309711067:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((5914983247:ℚ)/10000000000),((3038179761:ℚ)/5000000000),((51004882729:ℚ)/57200000000),((11098539283:ℚ)/11345000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((21214463:ℚ)/31250000),((-538134998482186543157951395293762036668979016587614653839:ℚ)/1492985465924631250000000000000000000000000000000000000000),((-464048306646214199548607787:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((2987233789:ℚ)/5000000000),((3067964929:ℚ)/5000000000),((25710636523:ℚ)/28837500000),((11187894787:ℚ)/11440000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((6662996581:ℚ)/10000000000),((-299504191507351615357393804554315436961464271995273173134933:ℚ)/830045748348960000000000000000000000000000000000000000000000),((-6083920225056811459114737:ℚ)/12160000000000000000000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((4633:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((754243763:ℚ)/1250000000),((6165713819:ℚ)/10000000000),((6479706341:ℚ)/7239062500),((22465141457:ℚ)/23070000000),((1905827251:ℚ)/2000000000),((1907725537:ℚ)/2000000000),((3080928657:ℚ)/10000000000),((6535328487:ℚ)/10000000000),((-1602636782985656907416755313809406708855071360090234949377543:ℚ)/4392544132295820450000000000000000000000000000000000000000000),((-7212419325730508445359167:ℚ)/14440000000000000000000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4633:ℚ)/6400),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((378980669:ℚ)/625000000),((1548874247:ℚ)/2500000000),((3252864683:ℚ)/3634375000),((5638622741:ℚ)/5791250000),((9519843613:ℚ)/10000000000),((476456813:ℚ)/500000000),((622285377:ℚ)/2000000000),((647069229:ℚ)/1000000000),((-299663536872403894041241277651873917025708112736023724273:ℚ)/820968305131091021728515625000000000000000000000000000000),((-94728742267397117836117:ℚ)/190000000000000000000000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1163:ℚ)/1600),((4671:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((6093430869:ℚ)/10000000000),((9960447:ℚ)/16000000),((1935333929:ℚ)/2162500000),((36230141:ℚ)/37216000),((148605427:ℚ)/156250000),((4759921809:ℚ)/5000000000),((98156347:ℚ)/312500000),((256219973:ℚ)/400000000),((-528134457467443046313334739222002724027032135321171:ℚ)/1446280603544463360000000000000000000000000000000000),((-1379779937152518084675956569:ℚ)/2772480000000000000000000000)⟩
theorem valid11 : Valid source32 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((4671:ℚ)/6400) :=
  cell_of_packet source32 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4671:ℚ)/6400),((469:ℚ)/640),((7:ℚ)/8),((15:ℚ)/16),((1530792651:ℚ)/2500000000),((6255060989:ℚ)/10000000000),((13115548557:ℚ)/14656250000),((22733182967:ℚ)/23355000000),((9501845013:ℚ)/10000000000),((9510747333:ℚ)/10000000000),((792422551:ℚ)/2500000000),((633973207:ℚ)/1000000000),((-3838741874418611465629659076545068409129226451106368701416073:ℚ)/10507915410597783281250000000000000000000000000000000000000000),((-86079931230612082798429129:ℚ)/173280000000000000000000000)⟩
theorem valid12 : Valid source32 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source32 nn0 nn1 Qcell ((4671:ℚ)/6400) ((469:ℚ)/640) :=
  cell_of_packet source32 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((1230581983:ℚ)/2000000000),((78560523:ℚ)/125000000),((10534073881:ℚ)/11772500000),((285281569:ℚ)/293125000),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((1254674423:ℚ)/2000000000),((-136000944915322211864162383890022895408593556148648993:ℚ)/372128677935867309570312500000000000000000000000000000),((-18330382585117659367354827:ℚ)/36966400000000000000000000)⟩
theorem valid13 : Valid source32 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source32 nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet source32 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((6182648807:ℚ)/10000000000),((3157310969:ℚ)/5000000000),((52878541649:ℚ)/59100000000),((11455932907:ℚ)/11772500000),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3103200049:ℚ)/5000000000),((-21703569706119371194655855371332600608904599789866415904797:ℚ)/59362177894345620117187500000000000000000000000000000000000),((-457426439612005544257222107:ℚ)/924160000000000000000000000)⟩
theorem valid14 : Valid source32 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source32 nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((1242477457:ℚ)/2000000000),((6344401291:ℚ)/10000000000),((10617342199:ℚ)/11867500000),((23001203873:ℚ)/23640000000),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((1227759127:ℚ)/2000000000),((-408321489020130034190976566342947432161830011382472723312787423:ℚ)/1116380257857513360000000000000000000000000000000000000000000000),((-18263743651024159211116907:ℚ)/36966400000000000000000000)⟩
theorem valid15 : Valid source32 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet source32 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((6242125353:ℚ)/10000000000),((1593544977:ℚ)/2500000000),((53294877471:ℚ)/59575000000),((5772634931:ℚ)/5933750000),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((6070537247:ℚ)/10000000000),((-135656599832790294295766761141663517062245906902881056888503:ℚ)/370753995987153410034179687500000000000000000000000000000000),((-1367283058042502363864099761:ℚ)/2772480000000000000000000000)⟩
theorem valid16 : Valid source32 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source32 nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((3135931509:ℚ)/5000000000),((643373497:ℚ)/1000000000),((26751520563:ℚ)/30025000000),((2326920491:ℚ)/2383000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3000801131:ℚ)/5000000000),((-552841779795424379274230259100247894470721251595167264727:ℚ)/1524923903728491171875000000000000000000000000000000000000),((-340532059652195817275860249:ℚ)/693120000000000000000000000)⟩
theorem valid17 : Valid source32 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source32 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((6331337153:ℚ)/10000000000),((6493287193:ℚ)/10000000000),((53919360071:ℚ)/60525000000),((23447861579:ℚ)/24020000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((117232107:ℚ)/200000000),((-4093444015357564776413408023152811732261728482520478616169127:ℚ)/11281740128276490000000000000000000000000000000000000000000000),((-452379023984870535744590987:ℚ)/924160000000000000000000000)⟩
theorem valid18 : Valid source32 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source32 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((49928201:ℚ)/78125000),((1638209161:ℚ)/2500000000),((424497407:ℚ)/476562500),((5906627483:ℚ)/6052500000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2859298033:ℚ)/5000000000),((-374482512057995724147702984793547193484407188492492057839:ℚ)/1031274020691035156250000000000000000000000000000000000000),((-440152736584692675408613:ℚ)/902500000000000000000000)⟩
theorem valid19 : Valid source32 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source32 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source32 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((322514039:ℚ)/500000000),((3335963743:ℚ)/5000000000),((2737598273:ℚ)/3097500000),((11991891229:ℚ)/12200000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1393084877:ℚ)/2500000000),((-103551729618625346440689885875415838072438842470515963324531:ℚ)/290369416417500000000000000000000000000000000000000000000000),((-1118208073070005044151003:ℚ)/2310400000000000000000000)⟩
theorem valid20 : Valid source32 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((1313843691:ℚ)/2000000000),((6791007989:ℚ)/10000000000),((11116905837:ℚ)/12580000000),((24341023967:ℚ)/24780000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1053796923:ℚ)/2000000000),((-375077356749062660323517634947372974205031833983081925797:ℚ)/1049825731819306640625000000000000000000000000000000000000),((-53275634785109879707525849:ℚ)/110899200000000000000000000)⟩
theorem valid21 : Valid source32 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source32 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((418009403:ℚ)/625000000),((219660619:ℚ)/312500000),((3526065821:ℚ)/4050000000),((782981857:ℚ)/786250000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((4948924473:ℚ)/10000000000),((-458136981854864919887169004399089403329691772164602943:ℚ)/1328742332380371093750000000000000000000000000000000000),((-1707444869790806307343987:ℚ)/3610000000000000000000000)⟩
theorem valid22 : Valid source32 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source32 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((692599839:ℚ)/1000000000),((1596266869:ℚ)/2000000000),((5808198873:ℚ)/7240000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((4243280711:ℚ)/10000000000),((-244977269290747398496461775132679759:ℚ)/786264000000000000000000000000000000),((-12617641293801437843152609:ℚ)/27724800000000000000000000)⟩
theorem valid23 : Valid source32 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((7877207197:ℚ)/10000000000),((446655537:ℚ)/500000000),((64740450379:ℚ)/80000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-10103453760919026675226175869592763517:ℚ)/32000000000000000000000000000000000000),((-730611:ℚ)/1600000)⟩
theorem valid24 : Valid source32 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source32 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((2207046493:ℚ)/2500000000),((12737766319:ℚ)/10000000000),((17849325451:ℚ)/27600000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-28909089233816501985163339:ℚ)/126960000000000000000000000),((-730611:ℚ)/1600000)⟩
theorem valid25 : Valid source32 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet25 valid25
private theorem node1_3 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source32 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source32 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source32 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_6 node6_13
private theorem node14_16 :
    CellBound source32 nn0 nn1 Qcell ((4709:ℚ)/6400) ((4747:ℚ)/6400) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source32 nn0 nn1 Qcell ((469:ℚ)/640) ((4747:ℚ)/6400) :=
  cell_join leaf13 node14_16
private theorem node17_19 :
    CellBound source32 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source32 nn0 nn1 Qcell ((4747:ℚ)/6400) ((2421:ℚ)/3200) :=
  cell_join leaf16 node17_19
private theorem node13_19 :
    CellBound source32 nn0 nn1 Qcell ((469:ℚ)/640) ((2421:ℚ)/3200) :=
  cell_join node13_16 node16_19
private theorem node20_22 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound source32 nn0 nn1 Qcell ((2421:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join leaf19 node20_22
private theorem node22_24 :
    CellBound source32 nn0 nn1 Qcell ((629:ℚ)/800) ((181:ℚ)/200) :=
  cell_join leaf22 leaf23
private theorem node24_26 :
    CellBound source32 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf24 leaf25
private theorem node22_26 :
    CellBound source32 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node22_24 node24_26
private theorem node19_26 :
    CellBound source32 nn0 nn1 Qcell ((2421:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node19_22 node22_26
private theorem node13_26 :
    CellBound source32 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node13_19 node19_26
private theorem node0_26 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_13 node13_26
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_26
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25]
theorem packet_count : packets.length = 26 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC31
#check @N11Formalization.C450Source32GroupedC31.bound
#print axioms N11Formalization.C450Source32GroupedC31.valid0
#print axioms N11Formalization.C450Source32GroupedC31.valid1
#print axioms N11Formalization.C450Source32GroupedC31.valid2
#print axioms N11Formalization.C450Source32GroupedC31.valid3
#print axioms N11Formalization.C450Source32GroupedC31.valid4
#print axioms N11Formalization.C450Source32GroupedC31.valid5
#print axioms N11Formalization.C450Source32GroupedC31.valid6
#print axioms N11Formalization.C450Source32GroupedC31.valid7
#print axioms N11Formalization.C450Source32GroupedC31.valid8
#print axioms N11Formalization.C450Source32GroupedC31.valid9
#print axioms N11Formalization.C450Source32GroupedC31.valid10
#print axioms N11Formalization.C450Source32GroupedC31.valid11
#print axioms N11Formalization.C450Source32GroupedC31.valid12
#print axioms N11Formalization.C450Source32GroupedC31.valid13
#print axioms N11Formalization.C450Source32GroupedC31.valid14
#print axioms N11Formalization.C450Source32GroupedC31.valid15
#print axioms N11Formalization.C450Source32GroupedC31.valid16
#print axioms N11Formalization.C450Source32GroupedC31.valid17
#print axioms N11Formalization.C450Source32GroupedC31.valid18
#print axioms N11Formalization.C450Source32GroupedC31.valid19
#print axioms N11Formalization.C450Source32GroupedC31.valid20
#print axioms N11Formalization.C450Source32GroupedC31.valid21
#print axioms N11Formalization.C450Source32GroupedC31.valid22
#print axioms N11Formalization.C450Source32GroupedC31.valid23
#print axioms N11Formalization.C450Source32GroupedC31.valid24
#print axioms N11Formalization.C450Source32GroupedC31.valid25
#print axioms N11Formalization.C450Source32GroupedC31.bound
#print axioms N11Formalization.C450Source32GroupedC31.endpoint_checks
