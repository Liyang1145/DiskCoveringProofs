import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((13:ℚ)/16),((7:ℚ)/8),((5085869061:ℚ)/10000000000),((2712188707:ℚ)/5000000000),((85316297793:ℚ)/103000000000),((23945320949:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2094184197:ℚ)/2500000000),((-8398168794331685287395006173484738094164943:ℚ)/25284217520000000000000000000000000000000000),((-942680829790507660310111401:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((5324448589:ℚ)/10000000000),((5663241487:ℚ)/10000000000),((88417831657:ℚ)/106800000000),((49562690409:ℚ)/51500000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((39728943:ℚ)/50000000),((-5314823417921355717572876486018247050361680692362690790151:ℚ)/15848676575317382812500000000000000000000000000000000000000),((-3714539996511676934605382081:ℚ)/7393280000000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((556295081:ℚ)/1000000000),((722829683:ℚ)/1250000000),((9151836053:ℚ)/10870000000),((2099935927:ℚ)/2225000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7495915669:ℚ)/10000000000),((-17210239702683877912324942385459055234309864339149267584697:ℚ)/48806807599277343750000000000000000000000000000000000000000),((-57596767956704608949882761:ℚ)/115520000000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((1420543871:ℚ)/2500000000),((92218923:ℚ)/156250000),((3323867189:ℚ)/3950000000),((800532461:ℚ)/849218750),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((7262729631:ℚ)/10000000000),((-10131810655975320947339739800490242327915794638443910683:ℚ)/28666466847263574600219726562500000000000000000000000000),((-2678961854872111230109963:ℚ)/5415000000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((13:ℚ)/16),((7:ℚ)/8),((1160276751:ℚ)/2000000000),((1204272691:ℚ)/2000000000),((6307865921:ℚ)/7500000000),((10413908837:ℚ)/11060000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3511643171:ℚ)/5000000000),((-12224081281170820670948832542995958211533582606308441:ℚ)/34512730000000000000000000000000000000000000000000000),((-145159525172929359244277769:ℚ)/295731200000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((5920576459:ℚ)/10000000000),((760129003:ℚ)/1250000000),((96167493967:ℚ)/113450000000),((6560903021:ℚ)/7031250000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6776898989:ℚ)/10000000000),((-808837731314244261744287710787017004686227224506964663916473:ℚ)/2237054806351661682128906250000000000000000000000000000000000),((-56477815972996065392249241:ℚ)/115520000000000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((5980167221:ℚ)/10000000000),((3070347841:ℚ)/5000000000),((96942173873:ℚ)/114400000000),((26452434887:ℚ)/28362500000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1662713409:ℚ)/2500000000),((-131878072403380838558225943308210560870214437831097613069:ℚ)/364498404766755676269531250000000000000000000000000000000),((-900032403506897267750447969:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((6039754379:ℚ)/10000000000),((6200354551:ℚ)/10000000000),((97716806927:ℚ)/115350000000),((53322481857:ℚ)/57200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((815344609:ℚ)/1250000000),((-12521224932186294498698382569251828761918113266526720347060741:ℚ)/34585239514540000000000000000000000000000000000000000000000000),((-3585636285744380180984057649:ℚ)/7393280000000000000000000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((243973521:ℚ)/400000000),((6260008749:ℚ)/10000000000),((3939655773:ℚ)/4652000000),((53740061243:ℚ)/57675000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3196241217:ℚ)/5000000000),((-1566727788698646226487247604350091077189706454775928679294797:ℚ)/4324849396020850781250000000000000000000000000000000000000000),((-10713300657576375620835622747:ℚ)/22179840000000000000000000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((13:ℚ)/16),((7:ℚ)/8),((1539729561:ℚ)/2500000000),((789957299:ℚ)/1250000000),((24816484293:ℚ)/29312500000),((6769701093:ℚ)/7268750000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((6259891407:ℚ)/10000000000),((-9568678960608598549570054460262921891961573869001604232921:ℚ)/26398235768727645874023437500000000000000000000000000000000),((-55570646816913063370243849:ℚ)/115520000000000000000000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6218495121:ℚ)/10000000000),((637930359:ℚ)/1000000000),((33346812191:ℚ)/39400000000),((5457512513:ℚ)/5862500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((6124830359:ℚ)/10000000000),((-1889636661311257395451056991120173594073434997980696441:ℚ)/5210245635375976562500000000000000000000000000000000000),((-106256994001739858863721107:ℚ)/221798400000000000000000000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((12261853:ℚ)/19531250),((128778889:ℚ)/200000000),((787616356:ℚ)/930859375),((1099852223:ℚ)/1182000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((37419557:ℚ)/62500000),((-12760976416533506057424472477210055402636449803714067803433:ℚ)/35166713400357570000000000000000000000000000000000000000000),((-1410894165590376365754929:ℚ)/2957312000000000000000000)⟩
theorem valid11 : Valid source32 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((6337639169:ℚ)/10000000000),((1624645269:ℚ)/2500000000),((101589309197:ℚ)/120100000000),((13852516883:ℚ)/14893750000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((5846598097:ℚ)/10000000000),((-4223882566578010195294580752882226875316896278277776871417:ℚ)/11634246091678552031517028808593750000000000000000000000000),((-658599041609803876907550667:ℚ)/1386240000000000000000000000)⟩
theorem valid12 : Valid source32 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source32 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((3198603247:ℚ)/5000000000),((6558213569:ℚ)/10000000000),((51181842211:ℚ)/60525000000),((55827494983:ℚ)/60050000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((1425756257:ℚ)/2500000000),((-64029639820389768351389973902059448895510996661525411067532091:ℚ)/176277189504320156250000000000000000000000000000000000000000000),((-3497778208206342700062331489:ℚ)/7393280000000000000000000000)⟩
theorem valid13 : Valid source32 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source32 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((6456770787:ℚ)/10000000000),((3308921013:ℚ)/5000000000),((103138020231:ℚ)/122000000000),((28122447091:ℚ)/30262500000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((694521371:ℚ)/1250000000),((-46845802765838499587999602612706475225736952687837841678587:ℚ)/128909252586379394531250000000000000000000000000000000000000),((-2612239018390180257187471243:ℚ)/5544960000000000000000000000)⟩
theorem valid14 : Valid source32 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source32 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source32 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((3258166059:ℚ)/5000000000),((842135901:ℚ)/1250000000),((17318719589:ℚ)/20650000000),((7134951307:ℚ)/7625000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1081153073:ℚ)/2000000000),((-8450402691814084730341608584646267151161437012568858262599:ℚ)/23630323601684570312500000000000000000000000000000000000000),((-161872082290282474206212347:ℚ)/346560000000000000000000000)⟩
theorem valid15 : Valid source32 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6635446167:ℚ)/10000000000),((6856317341:ℚ)/10000000000),((105460800171:ℚ)/125800000000),((57914221387:ℚ)/61950000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1273255107:ℚ)/2500000000),((-5872974395077840472281392123038788507602530193918843422807:ℚ)/16403527059676666259765625000000000000000000000000000000000),((-3423385303726417122554748969:ℚ)/7393280000000000000000000000)⟩
theorem valid16 : Valid source32 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source32 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((6754549171:ℚ)/10000000000),((886841891:ℚ)/1250000000),((107009139223:ℚ)/129600000000),((7447893237:ℚ)/7862500000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((4761712159:ℚ)/10000000000),((-1844038650945929762541648833349562825587204813091129329937:ℚ)/5314969329521484375000000000000000000000000000000000000000),((-145563485627015552388929:ℚ)/320000000000000000000000)⟩
theorem valid17 : Valid source32 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source32 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((1748180999:ℚ)/2500000000),((8047922201:ℚ)/10000000000),((27526352987:ℚ)/36200000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((4024727049:ℚ)/10000000000),((-5742636747040115903726370887778330599:ℚ)/19656600000000000000000000000000000000),((-223893411:ℚ)/512000000)⟩
theorem valid18 : Valid source32 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((7945067827:ℚ)/10000000000),((9000501243:ℚ)/10000000000),((122485881751:ℚ)/160000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-37815781951428301764094286320235758837:ℚ)/128000000000000000000000000000000000000),((-223893411:ℚ)/512000000)⟩
theorem valid19 : Valid source32 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source32 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((1112120623:ℚ)/1250000000),((12807257619:ℚ)/10000000000),((16857568099:ℚ)/27600000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-26795102905236632608138939:ℚ)/126960000000000000000000000),((-223893411:ℚ)/512000000)⟩
theorem valid20 : Valid source32 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source32 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source32 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source32 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source32 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source32 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound source32 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound source32 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound source32 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC30
#check @N11Formalization.C450Source32GroupedC30.bound
#print axioms N11Formalization.C450Source32GroupedC30.valid0
#print axioms N11Formalization.C450Source32GroupedC30.valid1
#print axioms N11Formalization.C450Source32GroupedC30.valid2
#print axioms N11Formalization.C450Source32GroupedC30.valid3
#print axioms N11Formalization.C450Source32GroupedC30.valid4
#print axioms N11Formalization.C450Source32GroupedC30.valid5
#print axioms N11Formalization.C450Source32GroupedC30.valid6
#print axioms N11Formalization.C450Source32GroupedC30.valid7
#print axioms N11Formalization.C450Source32GroupedC30.valid8
#print axioms N11Formalization.C450Source32GroupedC30.valid9
#print axioms N11Formalization.C450Source32GroupedC30.valid10
#print axioms N11Formalization.C450Source32GroupedC30.valid11
#print axioms N11Formalization.C450Source32GroupedC30.valid12
#print axioms N11Formalization.C450Source32GroupedC30.valid13
#print axioms N11Formalization.C450Source32GroupedC30.valid14
#print axioms N11Formalization.C450Source32GroupedC30.valid15
#print axioms N11Formalization.C450Source32GroupedC30.valid16
#print axioms N11Formalization.C450Source32GroupedC30.valid17
#print axioms N11Formalization.C450Source32GroupedC30.valid18
#print axioms N11Formalization.C450Source32GroupedC30.valid19
#print axioms N11Formalization.C450Source32GroupedC30.valid20
#print axioms N11Formalization.C450Source32GroupedC30.bound
#print axioms N11Formalization.C450Source32GroupedC30.endpoint_checks
