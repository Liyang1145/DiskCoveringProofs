import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((840210327:ℚ)/1250000000),((6920698223:ℚ)/10000000000),((-78449076899:ℚ)/99200000000),((-2140630981:ℚ)/3159375000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((971042049:ℚ)/2000000000),((256344920707549421940690942218593572975415087822734252155888269:ℚ)/3118080687206400000000000000000000000000000000000000000000000000),((377080312115604595284224579:ℚ)/693120000000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((6840777851:ℚ)/10000000000),((7039735789:ℚ)/10000000000),((-79996565257:ℚ)/101100000000),((-17482333553:ℚ)/25750000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((1126979877:ℚ)/2500000000),((8449880856320247486551605730019916916681105819193519062906749:ℚ)/102777770508553125000000000000000000000000000000000000000000000),((8059181543041299904336207017:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((869982537:ℚ)/1250000000),((887406327:ℚ)/1250000000),((-10096282251:ℚ)/12875000000),((-2229947611:ℚ)/3248437500),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((4133730187:ℚ)/10000000000),((570472273898680112172879523151928312848692816774997184635069:ℚ)/7206770997935485839843750000000000000000000000000000000000000),((378050143274113322426938019:ℚ)/693120000000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((3509698471:ℚ)/5000000000),((222781471:ℚ)/312500000),((-2536159123:ℚ)/3248437500),((-9009095413:ℚ)/13053125000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((393416213:ℚ)/1000000000),((3299480695795496846950660902208894300023562010840565523027:ℚ)/42476609291644755005836486816406250000000000000000000000000),((2016998636705213935171984897:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((3524582079:ℚ)/5000000000),((7158762901:ℚ)/10000000000),((-81543917713:ℚ)/104425000000),((-9053746237:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3830698277:ℚ)/10000000000),((76067429275882619172580913952071190061530754175650927731086447:ℚ)/978936357801348059082031250000000000000000000000000000000000000),((6053750484191512595531719091:ℚ)/11089920000000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-13:ℚ)/16),((-3:ℚ)/4),((7078930649:ℚ)/10000000000),((7188518113:ℚ)/10000000000),((-81930735469:ℚ)/104900000000),((-18196791947:ℚ)/26343750000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((744901909:ℚ)/2000000000),((1992601190687211616257660197654061104408270595724729927502179:ℚ)/25634900465350031250000000000000000000000000000000000000000000),((8075336798441934590126518017:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((284347857:ℚ)/400000000),((3609136357:ℚ)/5000000000),((-41158772641:ℚ)/52687500000),((-731443571:ℚ)/1058500000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((1807677653:ℚ)/5000000000),((53091193843895296966205470500483298157295462342473822890205557:ℚ)/682799601387970733642578125000000000000000000000000000000000000),((38779214430004782405422099:ℚ)/70975488000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((892307687:ℚ)/1250000000),((3624013357:ℚ)/5000000000),((-41352173641:ℚ)/52925000000),((-2296923061:ℚ)/3322656250),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((1751478901:ℚ)/5000000000),((651762229328660698240730123227039375045644864998752060259503871:ℚ)/8379601911990454931640625000000000000000000000000000000000000000),((126291655267877679216343873:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((716822587:ℚ)/1000000000),((181944503:ℚ)/250000000),((-2077278539:ℚ)/2658125000),((-1846467761:ℚ)/2670000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((423374201:ℚ)/1250000000),((81383672218193838327523847380292386239180357192409667989:ℚ)/1046017025189409828186035156250000000000000000000000000000),((80863255921839819018508073:ℚ)/147865600000000000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7197989559:ℚ)/10000000000),((7307532941:ℚ)/10000000000),((-83477928233:ℚ)/106800000000),((-18553968677:ℚ)/26818750000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((81677059:ℚ)/250000000),((85237032011344888744918581427356838843769444024645330739325223:ℚ)/1095218660690634375000000000000000000000000000000000000000000000),((24269945917869321377732455331:ℚ)/44359680000000000000000000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-13:ℚ)/16),((-3:ℚ)/4),((722775257:ℚ)/1000000000),((114645081:ℚ)/156250000),((-1310386053:ℚ)/1676171875),((-1864325771:ℚ)/2693750000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3142771707:ℚ)/10000000000),((212820247736663206449395093495473546001562293420961608853:ℚ)/2733758898306476138532161712646484375000000000000000000000),((4259807936601065753562907:ℚ)/7782400000000000000000000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7257514913:ℚ)/10000000000),((7367036857:ℚ)/10000000000),((-84251479141:ℚ)/107750000000),((-18732544739:ℚ)/27056250000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((1506758317:ℚ)/5000000000),((356558992478598199819083449318588466128748269843164898654112371:ℚ)/4578856648317965698242187500000000000000000000000000000000000000),((8097284914088308242266933073:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid source20 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source20 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((7287276597:ℚ)/10000000000),((28893703:ℚ)/39062500),((-1322472556:ℚ)/1691015625),((-18821829791:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2878650541:ℚ)/10000000000),((200466293124174225058207780048279082997930386938412394221:ℚ)/2573646977266761660575866699218750000000000000000000000000),((24302794432294751562479196059:ℚ)/44359680000000000000000000000)⟩
theorem valid12 : Valid source20 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source20 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((7317037629:ℚ)/10000000000),((7456288529:ℚ)/10000000000),((-85411750877:ℚ)/108700000000),((-18911112887:ℚ)/27412500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2737343539:ℚ)/10000000000),((42539486574308986020344925279428980869729167847012276291148787:ℚ)/536183464491080468750000000000000000000000000000000000000000000),((24327012798566121495824988491:ℚ)/44359680000000000000000000000)⟩
theorem valid13 : Valid source20 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source20 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((7376557777:ℚ)/10000000000),((469736683:ℚ)/625000000),((-5386576879:ℚ)/6853125000),((-19089673331:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1215431933:ℚ)/5000000000),((9153769693380107793908027767950932145827654150691532215899:ℚ)/115344665013961064815521240234375000000000000000000000000000),((427172678207726791222783147:ℚ)/778240000000000000000000000)⟩
theorem valid14 : Valid source20 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source20 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-13:ℚ)/16),((-3:ℚ)/4),((7436075421:ℚ)/10000000000),((7634777453:ℚ)/10000000000),((-12533158127:ℚ)/15800000000),((-19268226263:ℚ)/28125000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2080721501:ℚ)/10000000000),((320395245631387856051867038315214452878409230154475177:ℚ)/3900015527343750000000000000000000000000000000000000000),((24381673612374842270814334091:ℚ)/44359680000000000000000000000)⟩
theorem valid15 : Valid source20 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source20 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((3777551729:ℚ)/5000000000),((1550751993:ℚ)/2000000000),((-1983975101:ℚ)/2500000000),((-9812655187:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1087498529:ℚ)/10000000000),((82002324191812090166418655980279259207128873360089765171:ℚ)/998486328125000000000000000000000000000000000000000000000),((2030999130607370719213722097:ℚ)/3696640000000000000000000000)⟩
theorem valid16 : Valid source20 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((1918530557:ℚ)/2500000000),((2176343507:ℚ)/2500000000),((-25412465591:ℚ)/28600000000),((-4995591671:ℚ)/8100000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((4737640343806266344376028756537515442352554149512115470147:ℚ)/39970254431250000000000000000000000000000000000000000000000),((112503679:ℚ)/204800000)⟩
theorem valid17 : Valid source20 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((4312993939:ℚ)/5000000000),((5303840247:ℚ)/5000000000),((-7021102579:ℚ)/7200000000),((-11418981817:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((32892316145610622105436069722009133434919167852609783:ℚ)/218700000000000000000000000000000000000000000000000000),((112503679:ℚ)/204800000)⟩
theorem valid18 : Valid source20 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((263216339:ℚ)/250000000),((3602596519:ℚ)/2500000000),(-1:ℚ),((-713649017:ℚ)/1380000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((41293102324414538436539:ℚ)/238050000000000000000000),((112503679:ℚ)/204800000)⟩
theorem valid19 : Valid source20 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet19 valid19
private theorem node0_2 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source20 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source20 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source20 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source20 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4291:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source20 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4291:ℚ)/6400) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((4291:ℚ)/6400) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source20 nn0 nn1 Qcell ((4291:ℚ)/6400) ((4329:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source20 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source20 nn0 nn1 Qcell ((4329:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source20 nn0 nn1 Qcell ((4291:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound source20 nn0 nn1 Qcell ((4291:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC04
#check @N11Formalization.C450Source20GroupedC04.bound
#print axioms N11Formalization.C450Source20GroupedC04.valid0
#print axioms N11Formalization.C450Source20GroupedC04.valid1
#print axioms N11Formalization.C450Source20GroupedC04.valid2
#print axioms N11Formalization.C450Source20GroupedC04.valid3
#print axioms N11Formalization.C450Source20GroupedC04.valid4
#print axioms N11Formalization.C450Source20GroupedC04.valid5
#print axioms N11Formalization.C450Source20GroupedC04.valid6
#print axioms N11Formalization.C450Source20GroupedC04.valid7
#print axioms N11Formalization.C450Source20GroupedC04.valid8
#print axioms N11Formalization.C450Source20GroupedC04.valid9
#print axioms N11Formalization.C450Source20GroupedC04.valid10
#print axioms N11Formalization.C450Source20GroupedC04.valid11
#print axioms N11Formalization.C450Source20GroupedC04.valid12
#print axioms N11Formalization.C450Source20GroupedC04.valid13
#print axioms N11Formalization.C450Source20GroupedC04.valid14
#print axioms N11Formalization.C450Source20GroupedC04.valid15
#print axioms N11Formalization.C450Source20GroupedC04.valid16
#print axioms N11Formalization.C450Source20GroupedC04.valid17
#print axioms N11Formalization.C450Source20GroupedC04.valid18
#print axioms N11Formalization.C450Source20GroupedC04.valid19
#print axioms N11Formalization.C450Source20GroupedC04.bound
#print axioms N11Formalization.C450Source20GroupedC04.endpoint_checks
