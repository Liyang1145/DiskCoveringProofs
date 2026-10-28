import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((6832434793:ℚ)/10000000000),((704065037:ℚ)/1000000000),((-4288455259:ℚ)/4960000000),((-75381652309:ℚ)/101100000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((45330511:ℚ)/100000000),((236759450854474280500655993363719681591805199334191154803:ℚ)/1396989555200000000000000000000000000000000000000000000000),((6295689857210550821937091:ℚ)/9241600000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((1737878953:ℚ)/2500000000),((7100147567:ℚ)/10000000000),((-43301032969:ℚ)/50550000000),((-19232426389:ℚ)/25512500000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((4160978351:ℚ)/10000000000),((1012425080522115360315848253901014634011745219257840746767:ℚ)/6218602879594482421875000000000000000000000000000000000000),((630831397523501987923329771:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7011051681:ℚ)/10000000000),((7129895313:ℚ)/10000000000),((-3346866707:ℚ)/3925000000),((-25901223951:ℚ)/34175000000),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((123834629:ℚ)/312500000),((42258774388729955213036827391233972857437961955131771629047:ℚ)/264830071299206542968750000000000000000000000000000000000000),((1894388079944240977261473473:ℚ)/2772480000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4101:ℚ)/6400),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((1760204623:ℚ)/2500000000),((3579821251:ℚ)/5000000000),((-21858748757:ℚ)/25631250000),((-19522660099:ℚ)/25750000000),((9864186891:ℚ)/10000000000),((9880131563:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((3859971433:ℚ)/10000000000),((267234953125917189586125814145957546212665649756301439987937:ℚ)/1674769664088384246826171875000000000000000000000000000000000),((158023512316931235000202339:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((4101:ℚ)/6400) ((103:ℚ)/160) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((707058457:ℚ)/1000000000),((3594694571:ℚ)/5000000000),((-21962861997:ℚ)/25750000000),((-7847759941:ℚ)/10347500000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((1877285863:ℚ)/5000000000),((1458473425705894676464269029199940621961434640134919227526451:ℚ)/9140555176937011718750000000000000000000000000000000000000000),((158181366387053464313286899:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4139:ℚ)/6400),((8297:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7100349923:ℚ)/10000000000),((3602131129:ℚ)/5000000000),((-22014917903:ℚ)/25868750000),((-78864548999:ℚ)/103712500000),((9840798677:ℚ)/10000000000),((1969704979:ℚ)/2000000000),((1786759881:ℚ)/10000000000),((3646277559:ℚ)/10000000000),((588350861980848357762426617344886303462008796867586903105363529:ℚ)/3724075980497987648773193359375000000000000000000000000000000000),((158260299087458424323350299:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((4139:ℚ)/6400) ((8297:ℚ)/12800) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((8297:ℚ)/12800),((2079:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((7115232331:ℚ)/10000000000),((7219135239:ℚ)/10000000000),((-44133946673:ℚ)/51856250000),((-79058020303:ℚ)/103950000000),((4916570841:ℚ)/5000000000),((4920399341:ℚ)/5000000000),((1829340989:ℚ)/10000000000),((897740831:ℚ)/2500000000),((168689573653055813602662148995309612833678034245869353490639:ℚ)/1067735646272558784484863281250000000000000000000000000000000),((1900070826838827207945743057:ℚ)/2772480000000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((8297:ℚ)/12800) ((2079:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2079:ℚ)/3200),((1667:ℚ)/2560),((-7:ℚ)/8),((-13:ℚ)/16),((3565057281:ℚ)/5000000000),((7234008087:ℚ)/10000000000),((-44238056609:ℚ)/51975000000),((-39625744653:ℚ)/52093750000),((4912776717:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((935297099:ℚ)/5000000000),((706964473:ℚ)/2000000000),((144476370265783555157527811887989870147740076382032442454857789:ℚ)/914462664189978186035156250000000000000000000000000000000000000),((1901018110138537847431210673:ℚ)/2772480000000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1667:ℚ)/2560) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1667:ℚ)/2560),((4177:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((893124577:ℚ)/1250000000),((3624440401:ℚ)/5000000000),((-22171082807:ℚ)/26046875000),((-9930619501:ℚ)/13053125000),((4909016731:ℚ)/5000000000),((9825553439:ℚ)/10000000000),((382121547:ℚ)/2000000000),((3477814581:ℚ)/10000000000),((38055966450806819302815983372398158824837585409831941985802769:ℚ)/240871744730117401480674743652343750000000000000000000000000000),((158497119912265403965138539:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((1667:ℚ)/2560) ((4177:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4177:ℚ)/6400),((8373:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((223746203:ℚ)/312500000),((1452750677:ℚ)/2000000000),((-8889254739:ℚ)/10442500000),((-2488700639:ℚ)/3270703125),((4905290651:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((194946007:ℚ)/1000000000),((854974137:ℚ)/2500000000),((9853903985700875905344087419534694281984544918106414317024757:ℚ)/62368552481476538781738281250000000000000000000000000000000000),((25372170844360283434476531:ℚ)/36966400000000000000000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8373:ℚ)/12800) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8373:ℚ)/12800),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((3587380101:ℚ)/5000000000),((7278625837:ℚ)/10000000000),((-14850126953:ℚ)/17443750000),((-39915941313:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((9810581307:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((420127643:ℚ)/1250000000),((720955912153055747406401376928820315034053508315229376141951:ℚ)/4563106113237013053894042968750000000000000000000000000000000),((634620077780104885705525891:ℚ)/924160000000000000000000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell ((8373:ℚ)/12800) ((1049:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1049:ℚ)/1600),((8411:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((898705217:ℚ)/1250000000),((7293498159:ℚ)/10000000000),((-44654487113:ℚ)/52450000000),((-10003167821:ℚ)/13142187500),((9795878581:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((1011977397:ℚ)/5000000000),((3301137069:ℚ)/10000000000),((5040052927967523068653114189674394506809092939728092133486346599:ℚ)/31899344969599112890625000000000000000000000000000000000000000000),((1904807699049347156010899777:ℚ)/2772480000000000000000000000)⟩
theorem valid11 : Valid source22 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source22 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8411:ℚ)/12800) :=
  cell_of_packet source22 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((8411:ℚ)/12800),((843:ℚ)/1280),((-7:ℚ)/8),((-13:ℚ)/16),((3602261549:ℚ)/5000000000),((456773147:ℚ)/625000000),((-2797412029:ℚ)/3285546875),((-40109400137:ℚ)/52687500000),((978862711:ℚ)/1000000000),((4897939293:ℚ)/5000000000),((2059717253:ℚ)/10000000000),((324018833:ℚ)/1000000000),((3982322192509419142934237761355515782150756720947809374769:ℚ)/25204503818531311690807342529296875000000000000000000000000),((2481452097026582544206451:ℚ)/3610000000000000000000000)⟩
theorem valid12 : Valid source22 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source22 nn0 nn1 Qcell ((8411:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_of_packet source22 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((843:ℚ)/1280),((8449:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((721940429:ℚ)/1000000000),((7323242417:ℚ)/10000000000),((-44862696919:ℚ)/52687500000),((-1148746511:ℚ)/1508750000),((4890720817:ℚ)/5000000000),((1957725423:ℚ)/2000000000),((83782417:ℚ)/400000000),((3178113599:ℚ)/10000000000),((26302087427671552161855731476047305135049999716499232764895193:ℚ)/166466690875214195251464843750000000000000000000000000000000000),((635567589267943513382163371:ℚ)/924160000000000000000000000)⟩
theorem valid13 : Valid source22 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source22 nn0 nn1 Qcell ((843:ℚ)/1280) ((8449:ℚ)/12800) :=
  cell_of_packet source22 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((8449:ℚ)/12800),((2117:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((7234285313:ℚ)/10000000000),((3669057177:ℚ)/5000000000),((-316667609:ℚ)/371875000),((-80605709069:ℚ)/105850000000),((9774321709:ℚ)/10000000000),((9781441639:ℚ)/10000000000),((425706267:ℚ)/2000000000),((3114845483:ℚ)/10000000000),((16257429041259039598907948377805912730966104963390897211:ℚ)/102892719725894927978515625000000000000000000000000000000),((476912592727549736856696593:ℚ)/693120000000000000000000000)⟩
theorem valid14 : Valid source22 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source22 nn0 nn1 Qcell ((8449:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2117:ℚ)/3200),((8487:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((906145771:ℚ)/1250000000),((1470597233:ℚ)/2000000000),((-9014180631:ℚ)/10585000000),((-246338903:ℚ)/323437500),((9767266893:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((2161672951:ℚ)/10000000000),((3050309647:ℚ)/10000000000),((2787995593476091256343971985072372788093966543788344783593:ℚ)/17644964552145703125000000000000000000000000000000000000000),((25447973599487639070204971:ℚ)/36966400000000000000000000)⟩
theorem valid15 : Valid source22 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source22 nn0 nn1 Qcell ((2117:ℚ)/3200) ((8487:ℚ)/12800) :=
  cell_of_packet source22 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((8487:ℚ)/12800),((4253:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((908005857:ℚ)/1250000000),((147357157:ℚ)/200000000),((-39282613:ℚ)/46125000),((-10124076141:ℚ)/13290625000),((9760276751:ℚ)/10000000000),((4883633449:ℚ)/5000000000),((438804929:ℚ)/2000000000),((1492211889:ℚ)/5000000000),((7125574797729270139109852992426142022922852250115857:ℚ)/45096705202313232421875000000000000000000000000000000),((254606095327544085421011:ℚ)/369664000000000000000000)⟩
theorem valid16 : Valid source22 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source22 nn0 nn1 Qcell ((8487:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((7278927379:ℚ)/10000000000),((3698800423:ℚ)/5000000000),((-22691602961:ℚ)/26581250000),((-81186055927:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((583419263:ℚ)/2000000000),((1334895633232584358353991387609454411681461618661636651034169:ℚ)/8368136201515278625488281250000000000000000000000000000000000),((159286770252245446624659931:ℚ)/231040000000000000000000000)⟩
theorem valid17 : Valid source22 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source22 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7308687931:ℚ)/10000000000),((7427343349:ℚ)/10000000000),((-15197134481:ℚ)/17800000000),((-81572943103:ℚ)/107275000000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((347211847:ℚ)/1250000000),((115544498780071137684646415474412145919064434916965578744201:ℚ)/724350966065234375000000000000000000000000000000000000000000),((637778985185531164684943539:ℚ)/924160000000000000000000000)⟩
theorem valid18 : Valid source22 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-7:ℚ)/8),((-13:ℚ)/16),((1467689567:ℚ)/2000000000),((3728542683:ℚ)/5000000000),((-22899798781:ℚ)/26818750000),((-16391964371:ℚ)/21550000000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2631120917:ℚ)/10000000000),((10465322390815650955845364668171742683730251940376327642803:ℚ)/65610213559355427324771881103515625000000000000000000000000),((478808213245257210793912313:ℚ)/693120000000000000000000000)⟩
theorem valid19 : Valid source22 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source22 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source22 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((3684103549:ℚ)/5000000000),((7516567967:ℚ)/10000000000),((-46215975769:ℚ)/53875000000),((-41173346137:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2476100631:ℚ)/10000000000),((93804875841456788645384681656955808060199638449480518669044967:ℚ)/577392262041497802734375000000000000000000000000000000000000000),((639675068022001563671860171:ℚ)/924160000000000000000000000)⟩
theorem valid20 : Valid source22 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source22 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((1485544747:ℚ)/2000000000),((7635527609:ℚ)/10000000000),((-47048693263:ℚ)/54350000000),((-16624081711:ℚ)/22120000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2133264649:ℚ)/10000000000),((24691695826752124437734858747390771020655612137300886496203:ℚ)/146772310257989501953125000000000000000000000000000000000000),((44421651:ℚ)/64000000)⟩
theorem valid21 : Valid source22 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source22 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((1509349937:ℚ)/2000000000),((7873425949:ℚ)/10000000000),((-48713981643:ℚ)/55300000000),((-16933549181:ℚ)/22880000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1184467633:ℚ)/10000000000),((276863460944088047253294602870398047210038304706954604129363:ℚ)/1543829909496875000000000000000000000000000000000000000000000),((44421651:ℚ)/64000000)⟩
theorem valid22 : Valid source22 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((1556954799:ℚ)/2000000000),((2206196307:ℚ)/2500000000),((-1258488559:ℚ)/1300000000),((-1950268043:ℚ)/2880000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((11266018377469881317151146241857212379669013425489419:ℚ)/46342968750000000000000000000000000000000000000000000),((44421651:ℚ)/64000000)⟩
theorem valid23 : Valid source22 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((4368281463:ℚ)/5000000000),((10726727831:ℚ)/10000000000),(-1:ℚ),((-50067659019:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((6558172702795613286675001719285159977:ℚ)/24000000000000000000000000000000000000),((44421651:ℚ)/64000000)⟩
theorem valid24 : Valid source22 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((5319559539:ℚ)/5000000000),((14529006853:ℚ)/10000000000),(-1:ℚ),((-20811424669:ℚ)/36800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((203428897676777645799563729:ℚ)/677120000000000000000000000),((44421651:ℚ)/64000000)⟩
theorem valid25 : Valid source22 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet25 valid25
private theorem node1_3 :
    CellBound source22 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4101:ℚ)/6400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((4101:ℚ)/6400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((8297:ℚ)/12800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source22 nn0 nn1 Qcell ((4101:ℚ)/6400) ((8297:ℚ)/12800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((8297:ℚ)/12800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source22 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source22 nn0 nn1 Qcell ((8297:ℚ)/12800) ((4177:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source22 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source22 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source22 nn0 nn1 Qcell ((4177:ℚ)/6400) ((843:ℚ)/1280) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source22 nn0 nn1 Qcell ((8297:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((843:ℚ)/1280) :=
  cell_join node0_6 node6_13
private theorem node14_16 :
    CellBound source22 nn0 nn1 Qcell ((8449:ℚ)/12800) ((8487:ℚ)/12800) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source22 nn0 nn1 Qcell ((843:ℚ)/1280) ((8487:ℚ)/12800) :=
  cell_join leaf13 node14_16
private theorem node17_19 :
    CellBound source22 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source22 nn0 nn1 Qcell ((8487:ℚ)/12800) ((4291:ℚ)/6400) :=
  cell_join leaf16 node17_19
private theorem node13_19 :
    CellBound source22 nn0 nn1 Qcell ((843:ℚ)/1280) ((4291:ℚ)/6400) :=
  cell_join node13_16 node16_19
private theorem node20_22 :
    CellBound source22 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound source22 nn0 nn1 Qcell ((4291:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join leaf19 node20_22
private theorem node22_24 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf22 leaf23
private theorem node24_26 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf24 leaf25
private theorem node22_26 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node22_24 node24_26
private theorem node19_26 :
    CellBound source22 nn0 nn1 Qcell ((4291:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node19_22 node22_26
private theorem node13_26 :
    CellBound source22 nn0 nn1 Qcell ((843:ℚ)/1280) ((69:ℚ)/50) :=
  cell_join node13_19 node19_26
private theorem node0_26 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_13 node13_26
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_26
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25]
theorem packet_count : packets.length = 26 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC03
#check @N11Formalization.C450Source22GroupedC03.bound
#print axioms N11Formalization.C450Source22GroupedC03.valid0
#print axioms N11Formalization.C450Source22GroupedC03.valid1
#print axioms N11Formalization.C450Source22GroupedC03.valid2
#print axioms N11Formalization.C450Source22GroupedC03.valid3
#print axioms N11Formalization.C450Source22GroupedC03.valid4
#print axioms N11Formalization.C450Source22GroupedC03.valid5
#print axioms N11Formalization.C450Source22GroupedC03.valid6
#print axioms N11Formalization.C450Source22GroupedC03.valid7
#print axioms N11Formalization.C450Source22GroupedC03.valid8
#print axioms N11Formalization.C450Source22GroupedC03.valid9
#print axioms N11Formalization.C450Source22GroupedC03.valid10
#print axioms N11Formalization.C450Source22GroupedC03.valid11
#print axioms N11Formalization.C450Source22GroupedC03.valid12
#print axioms N11Formalization.C450Source22GroupedC03.valid13
#print axioms N11Formalization.C450Source22GroupedC03.valid14
#print axioms N11Formalization.C450Source22GroupedC03.valid15
#print axioms N11Formalization.C450Source22GroupedC03.valid16
#print axioms N11Formalization.C450Source22GroupedC03.valid17
#print axioms N11Formalization.C450Source22GroupedC03.valid18
#print axioms N11Formalization.C450Source22GroupedC03.valid19
#print axioms N11Formalization.C450Source22GroupedC03.valid20
#print axioms N11Formalization.C450Source22GroupedC03.valid21
#print axioms N11Formalization.C450Source22GroupedC03.valid22
#print axioms N11Formalization.C450Source22GroupedC03.valid23
#print axioms N11Formalization.C450Source22GroupedC03.valid24
#print axioms N11Formalization.C450Source22GroupedC03.valid25
#print axioms N11Formalization.C450Source22GroupedC03.bound
#print axioms N11Formalization.C450Source22GroupedC03.endpoint_checks
