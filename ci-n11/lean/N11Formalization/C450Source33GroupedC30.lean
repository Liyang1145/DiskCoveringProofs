import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((13:ℚ)/16),((7:ℚ)/8),((157779829:ℚ)/312500000),((336830333:ℚ)/625000000),((2671137777:ℚ)/3218750000),((2997812331:ℚ)/3100000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1688382139:ℚ)/2000000000),((-25161478758751479977237331766129047:ℚ)/76711825000000000000000000000000000),((-30315571209130861444119171:ℚ)/57760000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((2643802671:ℚ)/5000000000),((1407060677:ℚ)/2500000000),((44289434723:ℚ)/53400000000),((12409424739:ℚ)/12875000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((8013501381:ℚ)/10000000000),((-461891623074217977672479500129135614230372959279646689:ℚ)/1391211075782775878906250000000000000000000000000000000),((-478038012957071099582129331:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((5526173709:ℚ)/10000000000),((5747682851:ℚ)/10000000000),((91680258217:ℚ)/108700000000),((16824593319:ℚ)/17800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7566670527:ℚ)/10000000000),((-1348319274347062008216203658582823401376541806568868774881:ℚ)/3831506515000000000000000000000000000000000000000000000000),((-7591996662020097191265510339:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((56454297:ℚ)/100000000),((2933549541:ℚ)/5000000000),((932305861:ℚ)/1106000000),((25654846787:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3667620257:ℚ)/5000000000),((-65578510037642839922669877567755334281904301969488444623:ℚ)/185787734503784179687500000000000000000000000000000000000),((-1883759054035053795305427059:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((5764668199:ℚ)/10000000000),((740849827:ℚ)/1250000000),((94780686587:ℚ)/111550000000),((6465948789:ℚ)/6912500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((7097743033:ℚ)/10000000000),((-23797754996772684061754700377718033742668519659492460541:ℚ)/65794104542236328125000000000000000000000000000000000000),((-117287891219651622432961731:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((13:ℚ)/16),((7:ℚ)/8),((5824281171:ℚ)/10000000000),((2993246313:ℚ)/5000000000),((95555655223:ℚ)/112500000000),((26072724191:ℚ)/27887500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((174412967:ℚ)/250000000),((-1920487563648742238791213459578117507257319440604390761:ℚ)/5304243350830078125000000000000000000000000000000000000),((-1869431624049267542454179291:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((58838901:ℚ)/100000000),((967389:ℚ)/1600000),((963305713:ℚ)/1134500000),((8410123:ℚ)/9000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((274140947:ℚ)/400000000),((-374671369440720400026687566534453596286366824439:ℚ)/1033813125000000000000000000000000000000000000000),((-190692878051547886019:ℚ)/378535936000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((371468443:ℚ)/625000000),((48846917:ℚ)/80000000),((6069089759:ℚ)/7150000000),((423848419:ℚ)/453800000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1682164503:ℚ)/2500000000),((-121193842987420550563384756764331193647876672577221:ℚ)/334094649717400000000000000000000000000000000000000),((-474884297863206146165171:ℚ)/946339840000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((3001548117:ℚ)/5000000000),((6165542881:ℚ)/10000000000),((48940125521:ℚ)/57675000000),((53398800167:ℚ)/57200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1650453157:ℚ)/2500000000),((-24493578416816897646109218888024613802151993351301056974317:ℚ)/67461455490000000000000000000000000000000000000000000000000),((-7391106272423431377998076779:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((4633:ℚ)/6400),((13:ℚ)/16),((7:ℚ)/8),((1212538727:ℚ)/2000000000),((619538013:ℚ)/1000000000),((19731003451:ℚ)/23165000000),((5360766091:ℚ)/5767500000),((1905827251:ℚ)/2000000000),((1907725537:ℚ)/2000000000),((3080928657:ℚ)/10000000000),((202277131:ℚ)/312500000),((-2718411766186471673193105708393263336044908219204286657:ℚ)/7407025908387890625000000000000000000000000000000000000),((-73765930114447498747153091:ℚ)/147865600000000000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4633:ℚ)/6400),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((76156137:ℚ)/125000000),((3112608073:ℚ)/5000000000),((1238029781:ℚ)/1453750000),((26908256511:ℚ)/28956250000),((9519843613:ℚ)/10000000000),((476456813:ℚ)/500000000),((622285377:ℚ)/2000000000),((6407568393:ℚ)/10000000000),((-16197555129869358214077374797171468725751252404363972341:ℚ)/44119104961902999877929687500000000000000000000000000000),((-1840514466141163377327554331:ℚ)/3696640000000000000000000000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1163:ℚ)/1600),((4671:ℚ)/6400),((13:ℚ)/16),((7:ℚ)/8),((3061143691:ℚ)/5000000000),((1251010189:ℚ)/2000000000),((16571622661:ℚ)/19462500000),((10805071323:ℚ)/11630000000),((148605427:ℚ)/156250000),((4759921809:ℚ)/5000000000),((98156347:ℚ)/312500000),((6341693711:ℚ)/10000000000),((-140546016305467831752132954210300488421473816604369527207:ℚ)/382690589387343750000000000000000000000000000000000000000),((-293900033070321269442443619:ℚ)/591462400000000000000000000)⟩
theorem valid11 : Valid source33 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((4671:ℚ)/6400) :=
  cell_of_packet source33 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4671:ℚ)/6400),((469:ℚ)/640),((13:ℚ)/16),((7:ℚ)/8),((3076041457:ℚ)/5000000000),((3142442271:ℚ)/5000000000),((49908538941:ℚ)/58625000000),((27117095897:ℚ)/29193750000),((9501845013:ℚ)/10000000000),((9510747333:ℚ)/10000000000),((792422551:ℚ)/2500000000),((627522567:ℚ)/1000000000),((-1148315244555272050854819176476540435888116280869855276161:ℚ)/3125688742967376708984375000000000000000000000000000000000),((-1833230473360120627076750699:ℚ)/3696640000000000000000000000)⟩
theorem valid12 : Valid source33 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source33 nn0 nn1 Qcell ((4671:ℚ)/6400) ((469:ℚ)/640) :=
  cell_of_packet source33 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((13:ℚ)/16),((7:ℚ)/8),((1236375513:ℚ)/2000000000),((6314716951:ℚ)/10000000000),((20040881669:ℚ)/23545000000),((54443018657:ℚ)/58625000000),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((1241628969:ℚ)/2000000000),((-7783161091883699488608731800259834839246464513794634429523:ℚ)/21178697321472167968750000000000000000000000000000000000000),((-7318321060472084837246290139:ℚ)/14786560000000000000000000000)⟩
theorem valid13 : Valid source33 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source33 nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet source33 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((1552917837:ℚ)/2500000000),((6344548187:ℚ)/10000000000),((25147931881:ℚ)/29550000000),((54651837309:ℚ)/58862500000),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((6140430779:ℚ)/10000000000),((-6923386309984328261526483282651632401377324371120929241083:ℚ)/18833178265972595214843750000000000000000000000000000000000),((-7303698323180053178509506291:ℚ)/14786560000000000000000000000)⟩
theorem valid14 : Valid source33 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source33 nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((6241464271:ℚ)/10000000000),((1601051799:ℚ)/2500000000),((100979035523:ℚ)/119150000000),((13767362593:ℚ)/14775000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((6072061919:ℚ)/10000000000),((-5249155991711711529127991169175375378531733426166166455181:ℚ)/14411453443154296875000000000000000000000000000000000000000),((-454649194917227243987890139:ℚ)/924160000000000000000000000)⟩
theorem valid15 : Valid source33 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((6301047583:ℚ)/10000000000),((80798271:ℚ)/125000000),((101753618579:ℚ)/120100000000),((693587897:ℚ)/744687500),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((296663377:ℚ)/500000000),((-7061829006983809202179810424544234382331696966871261:ℚ)/19374264932020902633666992187500000000000000000000000),((-1132029413452961121878699:ℚ)/2310400000000000000000000)⟩
theorem valid16 : Valid source33 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source33 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((3180313791:ℚ)/5000000000),((6523511747:ℚ)/10000000000),((51264079283:ℚ)/60525000000),((55904582229:ℚ)/60050000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((5791563699:ℚ)/10000000000),((-119509609066476363590324919524606310331710742963449472676513:ℚ)/327652768595390625000000000000000000000000000000000000000000),((-7215501672436357283055022851:ℚ)/14786560000000000000000000000)⟩
theorem valid17 : Valid source33 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source33 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((1605051087:ℚ)/2500000000),((2633263:ℚ)/4000000),((25825664131:ℚ)/30500000000),((22528841:ℚ)/24210000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((22586913:ℚ)/40000000),((-197454715578574878704423165797738486607634857237:ℚ)/540996207575625000000000000000000000000000000000),((-1149748378640759374091:ℚ)/2365849600000000000000)⟩
theorem valid18 : Valid source33 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source33 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source33 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((1295955591:ℚ)/2000000000),((6702436469:ℚ)/10000000000),((20815422683:ℚ)/24780000000),((57157055283:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2749255293:ℚ)/5000000000),((-2250493319639164845669947224224410738679940388740900206083:ℚ)/6277443281250000000000000000000000000000000000000000000000),((-7126515433488606208912880979:ℚ)/14786560000000000000000000000)⟩
theorem valid19 : Valid source33 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((1649728997:ℚ)/2500000000),((1364339871:ℚ)/2000000000),((26406476961:ℚ)/31450000000),((11598379097:ℚ)/12390000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((5190750063:ℚ)/10000000000),((-37456730357919744108642933539433581905296406496295283:ℚ)/104314957454223632812500000000000000000000000000000000),((-282670088534167621184059499:ℚ)/591462400000000000000000000)⟩
theorem valid20 : Valid source33 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source33 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((6718042243:ℚ)/10000000000),((3530089867:ℚ)/5000000000),((107174549159:ℚ)/129600000000),((29830629069:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((4865464437:ℚ)/10000000000),((-545922503977873400679251290294678944500259347809090418437:ℚ)/1574805727265625000000000000000000000000000000000000000000),((-1736542760110223917573804371:ℚ)/3696640000000000000000000000)⟩
theorem valid21 : Valid source33 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source33 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((6956261509:ℚ)/10000000000),((8013583987:ℚ)/10000000000),((110271399617:ℚ)/144800000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((2072751197:ℚ)/5000000000),((-24294154131316903081851919:ℚ)/84843750000000000000000000),((-92353453:ℚ)/204800000)⟩
theorem valid22 : Valid source33 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((3954379801:ℚ)/5000000000),((4483169297:ℚ)/5000000000),((61326937413:ℚ)/80000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-181136451153054391080713:ℚ)/625000000000000000000000),((-92353453:ℚ)/204800000)⟩
theorem valid23 : Valid source33 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source33 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((886078153:ℚ)/1000000000),((12773554253:ℚ)/10000000000),((13503015989:ℚ)/22080000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1110838899267547:ℚ)/5520000000000000),((-92353453:ℚ)/204800000)⟩
theorem valid24 : Valid source33 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet24 valid24
private theorem node1_3 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source33 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source33 nn0 nn1 Qcell ((4633:ℚ)/6400) ((4671:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source33 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4671:ℚ)/6400) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((4671:ℚ)/6400) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((4671:ℚ)/6400) :=
  cell_join node0_6 node6_12
private theorem node13_15 :
    CellBound source33 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source33 nn0 nn1 Qcell ((4671:ℚ)/6400) ((591:ℚ)/800) :=
  cell_join leaf12 node13_15
private theorem node16_18 :
    CellBound source33 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((2421:ℚ)/3200) :=
  cell_join leaf15 node16_18
private theorem node12_18 :
    CellBound source33 nn0 nn1 Qcell ((4671:ℚ)/6400) ((2421:ℚ)/3200) :=
  cell_join node12_15 node15_18
private theorem node19_21 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source33 nn0 nn1 Qcell ((2421:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join leaf18 node19_21
private theorem node21_23 :
    CellBound source33 nn0 nn1 Qcell ((629:ℚ)/800) ((181:ℚ)/200) :=
  cell_join leaf21 leaf22
private theorem node23_25 :
    CellBound source33 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf23 leaf24
private theorem node21_25 :
    CellBound source33 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node21_23 node23_25
private theorem node18_25 :
    CellBound source33 nn0 nn1 Qcell ((2421:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node18_21 node21_25
private theorem node12_25 :
    CellBound source33 nn0 nn1 Qcell ((4671:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node12_18 node18_25
private theorem node0_25 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_12 node12_25
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_25
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24]
theorem packet_count : packets.length = 25 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC30
#check @N11Formalization.C450Source33GroupedC30.bound
#print axioms N11Formalization.C450Source33GroupedC30.valid0
#print axioms N11Formalization.C450Source33GroupedC30.valid1
#print axioms N11Formalization.C450Source33GroupedC30.valid2
#print axioms N11Formalization.C450Source33GroupedC30.valid3
#print axioms N11Formalization.C450Source33GroupedC30.valid4
#print axioms N11Formalization.C450Source33GroupedC30.valid5
#print axioms N11Formalization.C450Source33GroupedC30.valid6
#print axioms N11Formalization.C450Source33GroupedC30.valid7
#print axioms N11Formalization.C450Source33GroupedC30.valid8
#print axioms N11Formalization.C450Source33GroupedC30.valid9
#print axioms N11Formalization.C450Source33GroupedC30.valid10
#print axioms N11Formalization.C450Source33GroupedC30.valid11
#print axioms N11Formalization.C450Source33GroupedC30.valid12
#print axioms N11Formalization.C450Source33GroupedC30.valid13
#print axioms N11Formalization.C450Source33GroupedC30.valid14
#print axioms N11Formalization.C450Source33GroupedC30.valid15
#print axioms N11Formalization.C450Source33GroupedC30.valid16
#print axioms N11Formalization.C450Source33GroupedC30.valid17
#print axioms N11Formalization.C450Source33GroupedC30.valid18
#print axioms N11Formalization.C450Source33GroupedC30.valid19
#print axioms N11Formalization.C450Source33GroupedC30.valid20
#print axioms N11Formalization.C450Source33GroupedC30.valid21
#print axioms N11Formalization.C450Source33GroupedC30.valid22
#print axioms N11Formalization.C450Source33GroupedC30.valid23
#print axioms N11Formalization.C450Source33GroupedC30.valid24
#print axioms N11Formalization.C450Source33GroupedC30.bound
#print axioms N11Formalization.C450Source33GroupedC30.endpoint_checks
