import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((13:ℚ)/16),((7:ℚ)/8),((1289878537:ℚ)/2500000000),((5494303731:ℚ)/10000000000),((21248420981:ℚ)/25750000000),((47740126117:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((206138863:ℚ)/250000000),((-2234714686472171321759842282853933006345827:ℚ)/6524959360000000000000000000000000000000000),((-4186449126976625674030076429:ℚ)/8871936000000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((5397958071:ℚ)/10000000000),((5732990669:ℚ)/10000000000),((88093454923:ℚ)/106800000000),((49410934683:ℚ)/51500000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((3904660939:ℚ)/5000000000),((-9092058543075511180766554279081073808671844221763704448737:ℚ)/26414460958862304687500000000000000000000000000000000000000),((-3802454695795480102543063:ℚ)/8192000000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((112726689:ℚ)/200000000),((1170460559:ℚ)/2000000000),((1823846957:ℚ)/2174000000),((10049223913:ℚ)/10680000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1436152:ℚ)/1953125),((-119468113090676811742071261790287115006662511132120407263721:ℚ)/333187806544400000000000000000000000000000000000000000000000),((-54447695896305014043883703:ℚ)/118292480000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((5755499541:ℚ)/10000000000),((238863819:ℚ)/400000000),((92741494033:ℚ)/110600000000),((2043246733:ℚ)/2174000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((284649433:ℚ)/400000000),((-8989731455829924801237596836290922087727618014557168527:ℚ)/25049140950696875000000000000000000000000000000000000000),((-6478248105200126548848029:ℚ)/14195097600000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((13:ℚ)/16),((7:ℚ)/8),((5874650297:ℚ)/10000000000),((6090869703:ℚ)/10000000000),((31430151287:ℚ)/37500000000),((51916087921:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6872709193:ℚ)/10000000000),((-162699452435988997208671492051366199923119384905512323359:ℚ)/452979581250000000000000000000000000000000000000000000000),((-4014041860857421637131957301:ℚ)/8871936000000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((5993787451:ℚ)/10000000000),((6150500189:ℚ)/10000000000),((95839236863:ℚ)/113450000000),((17444500441:ℚ)/18750000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6621759619:ℚ)/10000000000),((-2871029616710396549537422640313886524341329357192453909910393:ℚ)/7855775451660156250000000000000000000000000000000000000000000),((-1332179515602894673045703823:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((6053351141:ℚ)/10000000000),((3105063203:ℚ)/5000000000),((96613564833:ℚ)/114400000000),((26375442421:ℚ)/28362500000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((6493225969:ℚ)/10000000000),((-21317042569459292485977502910873383265027941182441081311127:ℚ)/58319744762680908203125000000000000000000000000000000000000),((-331582282955079578625978767:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((6112911683:ℚ)/10000000000),((3134874229:ℚ)/5000000000),((32462617293:ℚ)/38450000000),((26584119603:ℚ)/28600000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1590621261:ℚ)/2500000000),((-7902052962616609034172361092090185024980065180209748803253513:ℚ)/21615774696587500000000000000000000000000000000000000000000000),((-330115698884729637248441183:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((1234493831:ℚ)/2000000000),((126587329:ℚ)/200000000),((19632419803:ℚ)/23260000000),((357237101:ℚ)/384500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((6229394933:ℚ)/10000000000),((-7027659520903108109478553279619684985730933001958325231:ℚ)/19221552871203781250000000000000000000000000000000000000),((-1456598891759559877503:ℚ)/3276800000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((13:ℚ)/16),((7:ℚ)/8),((389501477:ℚ)/625000000),((4991391:ℚ)/7812500),((6183519201:ℚ)/7328125000),((84379474:ℚ)/90859375),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1523449689:ℚ)/2500000000),((-47131998828286521221063569160593637839634433314658807:ℚ)/128897635589490458369255065917968750000000000000000000),((-2396268746841340452209:ℚ)/5415000000000000000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((1572893797:ℚ)/2500000000),((1289718129:ℚ)/2000000000),((24927619361:ℚ)/29550000000),((10884026903:ℚ)/11725000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((744440293:ℚ)/1250000000),((-35744266040538983590566420991936303613931918186588232214893:ℚ)/97744208119653320312500000000000000000000000000000000000000),((-156332160545846616678925349:ℚ)/354877440000000000000000000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((6351123893:ℚ)/10000000000),((6508197039:ℚ)/10000000000),((100484610609:ℚ)/119150000000),((54837379273:ℚ)/59100000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((2907185727:ℚ)/5000000000),((-99239042902917271031337312870478161982475589715452587866458641:ℚ)/271348097224981250000000000000000000000000000000000000000000000),((-3890513377351493624969981669:ℚ)/8871936000000000000000000000)⟩
theorem valid11 : Valid source30 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((6410669817:ℚ)/10000000000),((26271199:ℚ)/40000000),((101258707621:ℚ)/120100000000),((221018393:ℚ)/238300000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2835064177:ℚ)/5000000000),((-2788756468969623021504161423314892109829736969071916483:ℚ)/7624619518642455859375000000000000000000000000000000000),((-20654265540680288914263:ℚ)/47316992000000000000000)⟩
theorem valid12 : Valid source30 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source30 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((258808521:ℚ)/400000000),((6627398867:ℚ)/10000000000),((4081310773:ℚ)/4842000000),((55671792069:ℚ)/60050000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((5522547653:ℚ)/10000000000),((-107465803849694568632780311206636333695491785347546898639825373:ℚ)/293795315840533593750000000000000000000000000000000000000000000),((-1284929410190096634827633007:ℚ)/2957312000000000000000000000)⟩
theorem valid13 : Valid source30 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source30 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((6529753581:ℚ)/10000000000),((3343497237:ℚ)/5000000000),((102806796553:ℚ)/122000000000),((28044480659:ℚ)/30262500000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2685675549:ℚ)/5000000000),((-2910878465359659464044186096294112651610579922726396875301:ℚ)/7957361270764160156250000000000000000000000000000000000000),((-959213421497222959937915741:ℚ)/2217984000000000000000000000)⟩
theorem valid14 : Valid source30 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source30 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source30 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((6589291549:ℚ)/10000000000),((1701543871:ℚ)/2500000000),((103580790137:ℚ)/123900000000),((14230807097:ℚ)/15250000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1043244213:ℚ)/2000000000),((-340680065749790190087603850724576253709742352183943472651643:ℚ)/945212944067382812500000000000000000000000000000000000000000),((-79184178622613783596693783:ℚ)/184832000000000000000000000)⟩
theorem valid15 : Valid source30 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6708359957:ℚ)/10000000000),((3462671703:ℚ)/5000000000),((105128679441:ℚ)/125800000000),((28878701921:ℚ)/30975000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((152895039:ℚ)/312500000),((-3833547910420796612653769429370475088471068358664018566937:ℚ)/10631915686827468872070312500000000000000000000000000000000),((-941158832391093913239025301:ℚ)/2217984000000000000000000000)⟩
theorem valid16 : Valid source30 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source30 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((6827418709:ℚ)/10000000000),((7163642303:ℚ)/10000000000),((106676443217:ℚ)/129600000000),((59425496121:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((4548098701:ℚ)/10000000000),((-70107102285136609775781052919013983517437117704424544640121:ℚ)/200092962993750000000000000000000000000000000000000000000000),((-1230549329734975420265868567:ℚ)/2957312000000000000000000000)⟩
theorem valid17 : Valid source30 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source30 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((3532754477:ℚ)/5000000000),((9068662237:ℚ)/10000000000),((54885808201:ℚ)/80000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((754548447:ℚ)/2000000000),((-2084840498682368913550978145287187189:ℚ)/8000000000000000000000000000000000000),((-410430041:ℚ)/1024000000)⟩
theorem valid18 : Valid source30 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((1793843759:ℚ)/2000000000),((12874545697:ℚ)/10000000000),((26903968867:ℚ)/44160000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-23013546931778637158660439:ℚ)/108339200000000000000000000),((-410430041:ℚ)/1024000000)⟩
theorem valid19 : Valid source30 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet19 valid19
private theorem node0_2 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source30 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source30 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source30 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source30 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source30 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source30 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound source30 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC30
#check @N11Formalization.C450Source30GroupedC30.bound
#print axioms N11Formalization.C450Source30GroupedC30.valid0
#print axioms N11Formalization.C450Source30GroupedC30.valid1
#print axioms N11Formalization.C450Source30GroupedC30.valid2
#print axioms N11Formalization.C450Source30GroupedC30.valid3
#print axioms N11Formalization.C450Source30GroupedC30.valid4
#print axioms N11Formalization.C450Source30GroupedC30.valid5
#print axioms N11Formalization.C450Source30GroupedC30.valid6
#print axioms N11Formalization.C450Source30GroupedC30.valid7
#print axioms N11Formalization.C450Source30GroupedC30.valid8
#print axioms N11Formalization.C450Source30GroupedC30.valid9
#print axioms N11Formalization.C450Source30GroupedC30.valid10
#print axioms N11Formalization.C450Source30GroupedC30.valid11
#print axioms N11Formalization.C450Source30GroupedC30.valid12
#print axioms N11Formalization.C450Source30GroupedC30.valid13
#print axioms N11Formalization.C450Source30GroupedC30.valid14
#print axioms N11Formalization.C450Source30GroupedC30.valid15
#print axioms N11Formalization.C450Source30GroupedC30.valid16
#print axioms N11Formalization.C450Source30GroupedC30.valid17
#print axioms N11Formalization.C450Source30GroupedC30.valid18
#print axioms N11Formalization.C450Source30GroupedC30.valid19
#print axioms N11Formalization.C450Source30GroupedC30.bound
#print axioms N11Formalization.C450Source30GroupedC30.endpoint_checks
