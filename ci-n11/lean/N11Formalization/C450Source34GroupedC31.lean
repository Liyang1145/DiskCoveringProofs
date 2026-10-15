import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((7:ℚ)/8),((15:ℚ)/16),((4945460959:ℚ)/10000000000),((5287605347:ℚ)/10000000000),((44858226713:ℚ)/51500000000),(1:ℚ),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1077832461:ℚ)/1250000000),((-16040457044762391:ℚ)/51500000000000000),((-1030025450180216947185721423:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((5183591221:ℚ)/10000000000),((2763086857:ℚ)/5000000000),((46525138547:ℚ)/53400000000),(1:ℚ),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((8202321187:ℚ)/10000000000),((-8216155240982511810037109:ℚ)/26074218750000000000000000),((-1016922323960200280627271703:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((5421676467:ℚ)/10000000000),((1129085941:ℚ)/2000000000),((48191735269:ℚ)/54350000000),((1410685941:ℚ)/1424000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7764888329:ℚ)/10000000000),((-6540386008544883248386408000302498279722645259743221571:ℚ)/19617313356800000000000000000000000000000000000000000000),((-159595511458065513383952919:ℚ)/291840000000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((5540703691:ℚ)/10000000000),((1441167051:ℚ)/2500000000),((49024925837:ℚ)/55300000000),((5379501153:ℚ)/5435000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3769390141:ℚ)/5000000000),((-1660949543799079574296259684139384280622614973961066791:ℚ)/4954339586767578125000000000000000000000000000000000000),((-1004252561649657475869516823:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((2829860679:ℚ)/5000000000),((728035147:ℚ)/1250000000),((24929024753:ℚ)/27887500000),((2712105441:ℚ)/2765000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((730710837:ℚ)/1000000000),((-14611816471033600524991426723871703438073823358491638441:ℚ)/42108226907031250000000000000000000000000000000000000000),((-750899561199948765397834909:ℚ)/1386240000000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((7:ℚ)/8),((15:ℚ)/16),((5719226761:ℚ)/10000000000),((1176778021:ℚ)/2000000000),((50274587327:ℚ)/56250000000),((4375134063:ℚ)/4462000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1797252887:ℚ)/2500000000),((-3284312576061475022882076531830639767181004772469911:ℚ)/9446165550000000000000000000000000000000000000000000),((-997947982755071015750586943:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((1155745991:ℚ)/2000000000),((5943495093:ℚ)/10000000000),((10138221937:ℚ)/11345000000),((7351495093:ℚ)/7500000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((3534651727:ℚ)/5000000000),((-2084033167795107255679517548569858644919252196424333003041:ℚ)/5982714843750000000000000000000000000000000000000000000000),((-39787956586594607970790623:ℚ)/73932800000000000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((2919115497:ℚ)/5000000000),((298664807:ℚ)/500000000),((25553808479:ℚ)/28481250000),((1107194421:ℚ)/1134500000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((6947898083:ℚ)/10000000000),((-84074567315785386736305828039426274900196360928776807:ℚ)/237648182873718750000000000000000000000000000000000000),((-744885098418878004160764541:ℚ)/1386240000000000000000000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((1466995181:ℚ)/2500000000),((6003096239:ℚ)/10000000000),((986843559:ℚ)/1100000000),((7411096239:ℚ)/7595000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((3443265031:ℚ)/5000000000),((-380861354449186825560924447366795079895722709577617379:ℚ)/1075716934960937500000000000000000000000000000000000000),((-61972350289360515844959063:ℚ)/115520000000000000000000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((7:ℚ)/8),((15:ℚ)/16),((2948864967:ℚ)/5000000000),((3016447701:ℚ)/5000000000),((25762054769:ℚ)/28718750000),((11161343103:ℚ)/11440000000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((213271941:ℚ)/312500000),((-761753076331578478876270973829779082560671002023042463209:ℚ)/2149876986400000000000000000000000000000000000000000000000),((-742451749626736271023346461:ℚ)/1386240000000000000000000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((5927478633:ℚ)/10000000000),((151567341:ℚ)/250000000),((51732350431:ℚ)/57675000000),((560302023:ℚ)/574375000),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((6762401271:ℚ)/10000000000),((-242203043772431424349304333201650188360138547509855053:ℚ)/683052691121292114257812500000000000000000000000000000),((-2964942945627563535960628861:ℚ)/5544960000000000000000000000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2307:ℚ)/3200),((4633:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((2978613413:ℚ)/5000000000),((1218498193:ℚ)/2000000000),((25970293891:ℚ)/28956250000),((1500098193:ℚ)/1538000000),((1905827251:ℚ)/2000000000),((1907725537:ℚ)/2000000000),((3080928657:ℚ)/10000000000),((837451751:ℚ)/1250000000),((-1495253057597133855521593803450228958104937628499054073:ℚ)/4213774738994000000000000000000000000000000000000000000),((-12982809882171115094328333:ℚ)/24320000000000000000000000)⟩
theorem valid11 : Valid source34 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source34 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_of_packet source34 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4633:ℚ)/6400),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((149674363:ℚ)/250000000),((6122287387:ℚ)/10000000000),((1303720541:ℚ)/1453750000),((22590862161:ℚ)/23165000000),((9519843613:ℚ)/10000000000),((476456813:ℚ)/500000000),((622285377:ℚ)/2000000000),((3318163087:ℚ)/5000000000),((-80214220939475256450660701204312432551696779064116203299:ℚ)/225889817404943359375000000000000000000000000000000000000),((-615670858184141681773427:ℚ)/1155200000000000000000000)⟩
theorem valid12 : Valid source34 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source34 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1163:ℚ)/1600),((9323:ℚ)/12800),((7:ℚ)/8),((15:ℚ)/16),((6016721721:ℚ)/10000000000),((383574079:ℚ)/625000000),((52357052047:ℚ)/58268750000),((1414722237:ℚ)/1453750000),((2378817769:ℚ)/2500000000),((4759921809:ℚ)/5000000000),((156316407:ℚ)/500000000),((1314504593:ℚ)/2000000000),((-16007388076259784800483756277986231723946706227260970023:ℚ)/44755343369387817382812500000000000000000000000000000000),((-2952952814796218166458334109:ℚ)/5544960000000000000000000000)⟩
theorem valid13 : Valid source34 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((9323:ℚ)/12800) :=
  cell_of_packet source34 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((9323:ℚ)/12800),((4671:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((3015797569:ℚ)/5000000000),((6152082919:ℚ)/10000000000),((8743527661:ℚ)/9731250000),((22680248757:ℚ)/23307500000),((148605427:ℚ)/156250000),((9515271081:ℚ)/10000000000),((98156347:ℚ)/312500000),((6540423281:ℚ)/10000000000),((-44083095425173039733685301960161358589301354382296570076177:ℚ)/123212766409445214843750000000000000000000000000000000000000),((-245877003827677859528730063:ℚ)/462080000000000000000000000)⟩
theorem valid14 : Valid source34 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source34 nn0 nn1 Qcell ((9323:ℚ)/12800) ((4671:ℚ)/6400) :=
  cell_of_packet source34 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4671:ℚ)/6400),((9361:ℚ)/12800),((7:ℚ)/8),((15:ℚ)/16),((1209293687:ℚ)/2000000000),((3083490177:ℚ)/5000000000),((457089383:ℚ)/508750000),((3787490177:ℚ)/3892500000),((1188284009:ℚ)/1250000000),((9510747333:ℚ)/10000000000),((157772791:ℚ)/500000000),((81352361:ℚ)/125000000),((-161078359454352763841879081579308385958529929316274538989:ℚ)/450071533315722656250000000000000000000000000000000000000),((-39307942876402037398366527:ℚ)/73932800000000000000000000)⟩
theorem valid15 : Valid source34 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source34 nn0 nn1 Qcell ((4671:ℚ)/6400) ((9361:ℚ)/12800) :=
  cell_of_packet source34 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((9361:ℚ)/12800),((469:ℚ)/640),((7:ℚ)/8),((15:ℚ)/16),((606134161:ℚ)/1000000000),((618187757:ℚ)/1000000000),((5266939127:ℚ)/5862500000),((206996661:ℚ)/212750000),((9501845013:ℚ)/10000000000),((9506272077:ℚ)/10000000000),((792422551:ℚ)/2500000000),((3237908857:ℚ)/5000000000),((-1443633521706752711235943850430784955913666014708431:ℚ)/4032399259472656250000000000000000000000000000000000),((-9818892746615284406799343:ℚ)/18483200000000000000000000)⟩
theorem valid16 : Valid source34 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source34 nn0 nn1 Qcell ((9361:ℚ)/12800) ((469:ℚ)/640) :=
  cell_of_packet source34 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((469:ℚ)/640),((9399:ℚ)/12800),((7:ℚ)/8),((15:ℚ)/16),((6076214667:ℚ)/10000000000),((6196774569:ℚ)/10000000000),((52773502669:ℚ)/58743750000),((3259189101:ℚ)/3350000000),((474873293:ℚ)/500000000),((4750922509:ℚ)/5000000000),((636742009:ℚ)/2000000000),((6443307671:ℚ)/10000000000),((-197726928887114552112918643106768126485019651236435261483:ℚ)/552123327539062500000000000000000000000000000000000000000),((-2943240370381778541705246661:ℚ)/5544960000000000000000000000)⟩
theorem valid17 : Valid source34 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source34 nn0 nn1 Qcell ((469:ℚ)/640) ((9399:ℚ)/12800) :=
  cell_of_packet source34 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((9399:ℚ)/12800),((4709:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((1218217521:ℚ)/2000000000),((6211671353:ℚ)/10000000000),((10575522647:ℚ)/11772500000),((7619671353:ℚ)/7832500000),((9493134321:ℚ)/10000000000),((1899493173:ℚ)/2000000000),((1598759513:ℚ)/5000000000),((32053283:ℚ)/50000000),((-202644328466846410314075223987070333867078321133248504629:ℚ)/565678808893097656250000000000000000000000000000000000000),((-117632534182128295023770509:ℚ)/221798400000000000000000000)⟩
theorem valid18 : Valid source34 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source34 nn0 nn1 Qcell ((9399:ℚ)/12800) ((4709:ℚ)/6400) :=
  cell_of_packet source34 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((4709:ℚ)/6400),((9437:ℚ)/12800),((7:ℚ)/8),((15:ℚ)/16),((763245053:ℚ)/1250000000),((6226567921:ℚ)/10000000000),((6622715371:ℚ)/7372656250),((22903703763:ℚ)/23545000000),((948885011:ℚ)/1000000000),((4746567163:ℚ)/5000000000),((802780177:ℚ)/2500000000),((6377862293:ℚ)/10000000000),((-68968053496451943551239422671957120003442609788409795488887:ℚ)/192464247224076757812500000000000000000000000000000000000000),((-15304097795120738543798747:ℚ)/28880000000000000000000000)⟩
theorem valid19 : Valid source34 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source34 nn0 nn1 Qcell ((4709:ℚ)/6400) ((9437:ℚ)/12800) :=
  cell_of_packet source34 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((9437:ℚ)/12800),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((3060416563:ℚ)/5000000000),((1560366069:ℚ)/2500000000),((8847638647:ℚ)/9850000000),((5737098207:ℚ)/5898125000),((4742306471:ℚ)/5000000000),((1897770023:ℚ)/2000000000),((806129637:ℚ)/2500000000),((6344922483:ℚ)/10000000000),((-3622246230229269086612001606566365181579851451057869163:ℚ)/10105275356521057128906250000000000000000000000000000000),((-244663386350202877504823527:ℚ)/462080000000000000000000000)⟩
theorem valid20 : Valid source34 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source34 nn0 nn1 Qcell ((9437:ℚ)/12800) ((591:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((6135705711:ℚ)/10000000000),((6271256351:ℚ)/10000000000),((53189939977:ℚ)/59337500000),((7679256351:ℚ)/7880000000),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((6311834849:ℚ)/10000000000),((-26255926740201572374846276857645958419624617536606523113:ℚ)/73690529200000000000000000000000000000000000000000000000),((-2930943759707639731894276429:ℚ)/5544960000000000000000000000)⟩
theorem valid21 : Valid source34 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet source34 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((1233090107:ℚ)/2000000000),((1575261897:ℚ)/2500000000),((10679630749:ℚ)/11915000000),((5781785691:ℚ)/5933750000),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((1561301631:ℚ)/2500000000),((-277345637663443235142094588956260347196802814217186905709:ℚ)/777914385201748657226562500000000000000000000000000000000),((-39014583158340130364949367:ℚ)/73932800000000000000000000)⟩
theorem valid22 : Valid source34 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source34 nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((2383:ℚ)/3200),((957:ℚ)/1280),((7:ℚ)/8),((15:ℚ)/16),((61951949:ℚ)/100000000),((6330837997:ℚ)/10000000000),((178687881:ℚ)/199375000),((23216513991:ℚ)/23830000000),((75681297:ℚ)/80000000),((2367032267:ℚ)/2500000000),((1650403157:ℚ)/5000000000),((772244691:ℚ)/1250000000),((-601561989748084620722496181003495913546293268102998000977:ℚ)/1686253424981640625000000000000000000000000000000000000000),((-97374848651192293889783:ℚ)/184832000000000000000000)⟩
theorem valid23 : Valid source34 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source34 nn0 nn1 Qcell ((2383:ℚ)/3200) ((957:ℚ)/1280) :=
  cell_of_packet source34 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((957:ℚ)/1280),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((1556234703:ℚ)/2500000000),((6360627587:ℚ)/10000000000),((13453642921:ℚ)/15012500000),((7768627587:ℚ)/7975000000),((4726187811:ℚ)/5000000000),((946016213:ℚ)/1000000000),((831186567:ℚ)/2500000000),((6110067013:ℚ)/10000000000),((-13590483199622506365682168511434672312101000738006352099:ℚ)/38072824764648437500000000000000000000000000000000000000),((-182274932882268674158613341:ℚ)/346560000000000000000000000)⟩
theorem valid24 : Valid source34 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source34 nn0 nn1 Qcell ((957:ℚ)/1280) ((1201:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((1201:ℚ)/1600),((4823:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((6254682277:ℚ)/10000000000),((6390416369:ℚ)/10000000000),((54022775939:ℚ)/60287500000),((23395249107:ℚ)/24020000000),((9444767421:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1673989387:ℚ)/5000000000),((1208302599:ℚ)/2000000000),((-21315457295220901655883709597496497136515699708038223418131:ℚ)/59678548054450000000000000000000000000000000000000000000000),((-970518044899458519560263607:ℚ)/1848320000000000000000000000)⟩
theorem valid25 : Valid source34 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source34 nn0 nn1 Qcell ((1201:ℚ)/1600) ((4823:ℚ)/6400) :=
  cell_of_packet source34 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((4823:ℚ)/6400),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((62844253:ℚ)/100000000),((6420204353:ℚ)/10000000000),((542309771:ℚ)/605250000),((23484613059:ℚ)/24115000000),((4718667711:ℚ)/5000000000),((4722383713:ℚ)/5000000000),((674104879:ℚ)/2000000000),((5972272269:ℚ)/10000000000),((-18958504651038522532650152156237734933330683623765010947047:ℚ)/53048928247247460937500000000000000000000000000000000000000),((-96890369450903741117847:ℚ)/184832000000000000000000)⟩
theorem valid26 : Valid source34 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source34 nn0 nn1 Qcell ((4823:ℚ)/6400) ((2421:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((1262833577:ℚ)/2000000000),((161994449:ℚ)/250000000),((178489099:ℚ)/200000000),((65731483:ℚ)/67250000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((5902320311:ℚ)/10000000000),((-671395364896368924027304308671777534658696972811:ℚ)/1900889550781250000000000000000000000000000000000),((-38622511637817102035390207:ℚ)/73932800000000000000000000)⟩
theorem valid27 : Valid source34 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source34 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source34 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((3186825883:ℚ)/5000000000),((6539348483:ℚ)/10000000000),((27427781181:ℚ)/30737500000),((23842045449:ℚ)/24400000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((1152035463:ℚ)/2000000000),((-19738222026723816087971534208692525211374656651489878541683:ℚ)/55814627900000000000000000000000000000000000000000000000000),((-240584268725295023195799287:ℚ)/462080000000000000000000000)⟩
theorem valid28 : Valid source34 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((160828349:ℚ)/250000000),((6598915993:ℚ)/10000000000),((460599481:ℚ)/516250000),((24020747979:ℚ)/24590000000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((701857121:ℚ)/1250000000),((-1941259088755939354048999210253563700965767382321008681473:ℚ)/5482865788506250000000000000000000000000000000000000000000),((-599446042964620137129883:ℚ)/1155200000000000000000000)⟩
theorem valid29 : Valid source34 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source34 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet29 valid29
def packet30 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((3246307253:ℚ)/5000000000),((839755281:ℚ)/1250000000),((27844150771:ℚ)/31450000000),((1015755281:ℚ)/1032500000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((5466102837:ℚ)/10000000000),((-1461852664603005194944526064747679453283170490562853:ℚ)/4225721656131744384765625000000000000000000000000000),((-238109737160789699051821847:ℚ)/462080000000000000000000000)⟩
theorem valid30 : Valid source34 packet30 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf30 :
    CellBound source34 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet30 valid30
def packet31 : Packet := ⟨((629:ℚ)/800),((1277:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((3305785401:ℚ)/5000000000),((854644657:ℚ)/1250000000),((28260497807:ℚ)/31925000000),((83565783:ℚ)/85000000),((2337671911:ℚ)/2500000000),((9372267491:ℚ)/10000000000),((181171659:ℚ)/500000000),((1031417067:ℚ)/2000000000),((-1700173675764828620217121814414511404602934421636883:ℚ)/4901485156250000000000000000000000000000000000000000),((-709502979256381144666037149:ℚ)/1386240000000000000000000000)⟩
theorem valid31 : Valid source34 packet31 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf31 :
    CellBound source34 nn0 nn1 Qcell ((629:ℚ)/800) ((1277:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet31 valid31
def packet32 : Packet := ⟨((1277:ℚ)/1600),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((1346104189:ℚ)/2000000000),((3478130757:ℚ)/5000000000),((3823576441:ℚ)/4320000000),((12546392271:ℚ)/12770000000),((9331481479:ℚ)/10000000000),((9350687649:ℚ)/10000000000),((735446993:ℚ)/2000000000),((483023113:ℚ)/1000000000),((-122194525664252912178426896307332870851167180959273947429:ℚ)/351411907443750000000000000000000000000000000000000000000),((-37583126385973745970644743:ℚ)/73932800000000000000000000)⟩
theorem valid32 : Valid source34 packet32 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf32 :
    CellBound source34 nn0 nn1 Qcell ((1277:ℚ)/1600) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet32 valid32
def packet33 : Packet := ⟨((81:ℚ)/100),((343:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((1712366301:ℚ)/2500000000),((7432580023:ℚ)/10000000000),((14546564107:ℚ)/17150000000),(1:ℚ),((57977633:ℚ)/62500000),((2332870371:ℚ)/2500000000),((1913736159:ℚ)/5000000000),((1120402843:ℚ)/2500000000),((-72887143908688094121262139:ℚ)/229687500000000000000000000),((-171084038800639744656405349:ℚ)/346560000000000000000000000)⟩
theorem valid33 : Valid source34 packet33 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf33 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((343:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet33 valid33
def packet34 : Packet := ⟨((343:ℚ)/400),((181:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((7325188317:ℚ)/10000000000),((7908759607:ℚ)/10000000000),((61516318219:ℚ)/72400000000),(1:ℚ),((9252071821:ℚ)/10000000000),((1855284257:ℚ)/2000000000),((1946075537:ℚ)/5000000000),((674346679:ℚ)/2500000000),((-57811095696744616191024933:ℚ)/181000000000000000000000000),((-2714344115665020214402095061:ℚ)/5544960000000000000000000000)⟩
theorem valid34 : Valid source34 packet34 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf34 :
    CellBound source34 nn0 nn1 Qcell ((343:ℚ)/400) ((181:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet34 valid34
def packet35 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((7800835367:ℚ)/10000000000),((1772156307:ℚ)/2000000000),((64845847569:ℚ)/80000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-1877279852681587734511657:ℚ)/6250000000000000000000000),((-15685989:ℚ)/32000000)⟩
theorem valid35 : Valid source34 packet35 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf35 :
    CellBound source34 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet35 valid35
def packet36 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((8751944739:ℚ)/10000000000),((6333039969:ℚ)/5000000000),((71503613173:ℚ)/110400000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-22406490204735611:ℚ)/110400000000000000),((-15685989:ℚ)/32000000)⟩
theorem valid36 : Valid source34 packet36 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf36 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet36 valid36
private theorem node0_2 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source34 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source34 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((4671:ℚ)/6400) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source34 nn0 nn1 Qcell ((9361:ℚ)/12800) ((9399:ℚ)/12800) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source34 nn0 nn1 Qcell ((4671:ℚ)/6400) ((9399:ℚ)/12800) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((9399:ℚ)/12800) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((9399:ℚ)/12800) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((9399:ℚ)/12800) :=
  cell_join node0_9 node9_18
private theorem node18_20 :
    CellBound source34 nn0 nn1 Qcell ((9399:ℚ)/12800) ((9437:ℚ)/12800) :=
  cell_join leaf18 leaf19
private theorem node20_22 :
    CellBound source34 nn0 nn1 Qcell ((9437:ℚ)/12800) ((4747:ℚ)/6400) :=
  cell_join leaf20 leaf21
private theorem node18_22 :
    CellBound source34 nn0 nn1 Qcell ((9399:ℚ)/12800) ((4747:ℚ)/6400) :=
  cell_join node18_20 node20_22
private theorem node22_24 :
    CellBound source34 nn0 nn1 Qcell ((4747:ℚ)/6400) ((957:ℚ)/1280) :=
  cell_join leaf22 leaf23
private theorem node25_27 :
    CellBound source34 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_join leaf25 leaf26
private theorem node24_27 :
    CellBound source34 nn0 nn1 Qcell ((957:ℚ)/1280) ((2421:ℚ)/3200) :=
  cell_join leaf24 node25_27
private theorem node22_27 :
    CellBound source34 nn0 nn1 Qcell ((4747:ℚ)/6400) ((2421:ℚ)/3200) :=
  cell_join node22_24 node24_27
private theorem node18_27 :
    CellBound source34 nn0 nn1 Qcell ((9399:ℚ)/12800) ((2421:ℚ)/3200) :=
  cell_join node18_22 node22_27
private theorem node27_29 :
    CellBound source34 nn0 nn1 Qcell ((2421:ℚ)/3200) ((2459:ℚ)/3200) :=
  cell_join leaf27 leaf28
private theorem node30_32 :
    CellBound source34 nn0 nn1 Qcell ((1239:ℚ)/1600) ((1277:ℚ)/1600) :=
  cell_join leaf30 leaf31
private theorem node29_32 :
    CellBound source34 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1277:ℚ)/1600) :=
  cell_join leaf29 node30_32
private theorem node27_32 :
    CellBound source34 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1277:ℚ)/1600) :=
  cell_join node27_29 node29_32
private theorem node32_34 :
    CellBound source34 nn0 nn1 Qcell ((1277:ℚ)/1600) ((343:ℚ)/400) :=
  cell_join leaf32 leaf33
private theorem node35_37 :
    CellBound source34 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf35 leaf36
private theorem node34_37 :
    CellBound source34 nn0 nn1 Qcell ((343:ℚ)/400) ((69:ℚ)/50) :=
  cell_join leaf34 node35_37
private theorem node32_37 :
    CellBound source34 nn0 nn1 Qcell ((1277:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node32_34 node34_37
private theorem node27_37 :
    CellBound source34 nn0 nn1 Qcell ((2421:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node27_32 node32_37
private theorem node18_37 :
    CellBound source34 nn0 nn1 Qcell ((9399:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node18_27 node27_37
private theorem node0_37 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_18 node18_37
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_37
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29,packet30,packet31,packet32,packet33,packet34,packet35,packet36]
theorem packet_count : packets.length = 37 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC31
#check @N11Formalization.C450Source34GroupedC31.bound
#print axioms N11Formalization.C450Source34GroupedC31.valid0
#print axioms N11Formalization.C450Source34GroupedC31.valid1
#print axioms N11Formalization.C450Source34GroupedC31.valid2
#print axioms N11Formalization.C450Source34GroupedC31.valid3
#print axioms N11Formalization.C450Source34GroupedC31.valid4
#print axioms N11Formalization.C450Source34GroupedC31.valid5
#print axioms N11Formalization.C450Source34GroupedC31.valid6
#print axioms N11Formalization.C450Source34GroupedC31.valid7
#print axioms N11Formalization.C450Source34GroupedC31.valid8
#print axioms N11Formalization.C450Source34GroupedC31.valid9
#print axioms N11Formalization.C450Source34GroupedC31.valid10
#print axioms N11Formalization.C450Source34GroupedC31.valid11
#print axioms N11Formalization.C450Source34GroupedC31.valid12
#print axioms N11Formalization.C450Source34GroupedC31.valid13
#print axioms N11Formalization.C450Source34GroupedC31.valid14
#print axioms N11Formalization.C450Source34GroupedC31.valid15
#print axioms N11Formalization.C450Source34GroupedC31.valid16
#print axioms N11Formalization.C450Source34GroupedC31.valid17
#print axioms N11Formalization.C450Source34GroupedC31.valid18
#print axioms N11Formalization.C450Source34GroupedC31.valid19
#print axioms N11Formalization.C450Source34GroupedC31.valid20
#print axioms N11Formalization.C450Source34GroupedC31.valid21
#print axioms N11Formalization.C450Source34GroupedC31.valid22
#print axioms N11Formalization.C450Source34GroupedC31.valid23
#print axioms N11Formalization.C450Source34GroupedC31.valid24
#print axioms N11Formalization.C450Source34GroupedC31.valid25
#print axioms N11Formalization.C450Source34GroupedC31.valid26
#print axioms N11Formalization.C450Source34GroupedC31.valid27
#print axioms N11Formalization.C450Source34GroupedC31.valid28
#print axioms N11Formalization.C450Source34GroupedC31.valid29
#print axioms N11Formalization.C450Source34GroupedC31.valid30
#print axioms N11Formalization.C450Source34GroupedC31.valid31
#print axioms N11Formalization.C450Source34GroupedC31.valid32
#print axioms N11Formalization.C450Source34GroupedC31.valid33
#print axioms N11Formalization.C450Source34GroupedC31.valid34
#print axioms N11Formalization.C450Source34GroupedC31.valid35
#print axioms N11Formalization.C450Source34GroupedC31.valid36
#print axioms N11Formalization.C450Source34GroupedC31.bound
#print axioms N11Formalization.C450Source34GroupedC31.endpoint_checks
