import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((6722722249:ℚ)/10000000000),((6924275303:ℚ)/10000000000),((-17572825909:ℚ)/24800000000),((-60509944739:ℚ)/101100000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4852278151:ℚ)/10000000000),((245977723804521897623881980954040503761812716912041890599077:ℚ)/1571613249600000000000000000000000000000000000000000000000000),((54324426968612379675873707:ℚ)/115520000000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((6841987089:ℚ)/10000000000),((1408695697:ℚ)/2000000000),((-3586087091:ℚ)/5055000000),((-61821857979:ℚ)/103000000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((2252133059:ℚ)/5000000000),((2011358219297447387803844082968272391276074479045566492839:ℚ)/12847221313569140625000000000000000000000000000000000000000),((54312201114525452906789147:ℚ)/115520000000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((435077051:ℚ)/625000000),((7103073829:ℚ)/10000000000),((-18109221487:ℚ)/25750000000),((-3945847561:ℚ)/6496875000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((33033857:ℚ)/80000000),((1255149850585225184780406614054218371304064986284620114978663:ℚ)/8236309711926269531250000000000000000000000000000000000000000),((105981076261999449467891:ℚ)/225625000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((3510424421:ℚ)/5000000000),((7132869989:ℚ)/10000000000),((-18198609967:ℚ)/25987500000),((-31894668631:ℚ)/52212500000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((3929175659:ℚ)/10000000000),((3270219952866961758985570331920970752195706426392291401095339:ℚ)/21748023957322114562988281250000000000000000000000000000000000),((13559203106918483759192387:ℚ)/28880000000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((8813319:ℚ)/12500000),((179066629:ℚ)/250000000),((-457199887:ℚ)/652656250),((-80146509:ℚ)/131125000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((765089181:ℚ)/2000000000),((8987064814564191560438392914176150733008880894705587641:ℚ)/59749533557211185246706008911132812500000000000000000000),((84739015023574888777:ℚ)/180500000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-3:ℚ)/4),((-11:ℚ)/16),((1770115119:ℚ)/2500000000),((1438491871:ℚ)/2000000000),((-3675475613:ℚ)/5245000000),((-5370422103:ℚ)/8781250000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((3718974067:ℚ)/10000000000),((53567982787874902082717811854990890104242793120980609099:ℚ)/356040284240972656250000000000000000000000000000000000000),((3389314630936412676318827:ℚ)/7220000000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((1777566171:ℚ)/2500000000),((7222252587:ℚ)/10000000000),((-18466757761:ℚ)/26343750000),((-16193227881:ℚ)/26462500000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((1804758471:ℚ)/5000000000),((12844845729917885391460392109408740928557681500442126477184901:ℚ)/85349950173496341705322265625000000000000000000000000000000000),((3389062867184901121554387:ℚ)/7220000000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((3570033919:ℚ)/5000000000),((725204487:ℚ)/1000000000),((-1855613461:ℚ)/2646250000),((-32550373109:ℚ)/53162500000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((3496793633:ℚ)/10000000000),((157679494332706234399638326706093865746925334567356265408603:ℚ)/1047450238998806866455078125000000000000000000000000000000000),((13555221240762014848749627:ℚ)/28880000000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((7169869953:ℚ)/10000000000),((1456367243:ℚ)/2000000000),((-3729101729:ℚ)/5316250000),((-21809523161:ℚ)/35600000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((1690238413:ℚ)/5000000000),((560016764115255486082023656139278209586978174599401272377:ℚ)/3719171645117901611328125000000000000000000000000000000000),((54216671364538011804024763:ℚ)/115520000000000000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((3599835521:ℚ)/5000000000),((1827906659:ℚ)/2500000000),((-4683719977:ℚ)/6675000000),((-32878190731:ℚ)/53637500000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((3260181313:ℚ)/10000000000),((5753173722346256884839764860137442318153923717233868156113:ℚ)/38198195476096343994140625000000000000000000000000000000000),((13553091271963700916025787:ℚ)/28880000000000000000000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-3:ℚ)/4),((-11:ℚ)/16),((90368389:ℚ)/125000000),((1468283229:ℚ)/2000000000),((-3764849687:ℚ)/5363750000),((-826052279:ℚ)/1346875000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3135448553:ℚ)/10000000000),((158147676531464070418237056621700642042571337089254144723:ℚ)/1049763416949686837196350097656250000000000000000000000000),((222894597609112125219:ℚ)/475000000000000000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7259270199:ℚ)/10000000000),((3685602377:ℚ)/5000000000),((-9456807131:ℚ)/13468750000),((-7379108021:ℚ)/12025000000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((3005725537:ℚ)/10000000000),((16637081712010716864946674358788870627615112146778764137993:ℚ)/110408387546247243881225585937500000000000000000000000000000),((54203474524209771197364907:ℚ)/115520000000000000000000000)⟩
theorem valid11 : Valid source22 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source22 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((3644534147:ℚ)/5000000000),((296039699:ℚ)/400000000),((-760119097:ℚ)/1082250000),((-33369875617:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1435167533:ℚ)/5000000000),((6355426658806670979821752360160443225116980472159499609:ℚ)/42166632075538623046875000000000000000000000000000000000),((13549722562516740047172563:ℚ)/28880000000000000000000000)⟩
theorem valid12 : Valid source22 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source22 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7318865417:ℚ)/10000000000),((7460565299:ℚ)/10000000000),((-19181695897:ℚ)/27175000000),((-3945148211:ℚ)/6450000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2728432879:ℚ)/10000000000),((4427325471946586654143548602982713407522532832599017366399:ℚ)/28989157898522949218750000000000000000000000000000000000000),((2853278825001807266983817:ℚ)/6080000000000000000000000)⟩
theorem valid13 : Valid source22 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source22 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((7378456797:ℚ)/10000000000),((7520134707:ℚ)/10000000000),((-19360404121:ℚ)/27412500000),((-67723024767:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((605115251:ℚ)/2500000000),((161104062676548450250368631408074336245037204201793658437159:ℚ)/1054579794413358306884765625000000000000000000000000000000000),((54202664857716783459863763:ℚ)/115520000000000000000000000)⟩
theorem valid14 : Valid source22 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source22 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/4),((-11:ℚ)/16),((7438044441:ℚ)/10000000000),((7639263627:ℚ)/10000000000),((-19717790881:ℚ)/27650000000),((-22792829617:ℚ)/37500000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((413628439:ℚ)/2000000000),((363761786409816010158082110572000292500693791842129703:ℚ)/2322405079650878906250000000000000000000000000000000000),((54204986054476724607261067:ℚ)/115520000000000000000000000)⟩
theorem valid15 : Valid source22 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source22 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((7557208897:ℚ)/10000000000),((7758379903:ℚ)/10000000000),((-20075139709:ℚ)/28125000000),((-69689297867:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((265417121:ℚ)/2500000000),((222659863857386013462215219957752058959220557149624443788967:ℚ)/1421672916412353515625000000000000000000000000000000000000000),((54111543629679731741045563:ℚ)/115520000000000000000000000)⟩
theorem valid16 : Valid source22 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source22 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((7676359517:ℚ)/10000000000),((435546099:ℚ)/500000000),((-1146638297:ℚ)/1430000000),((-70999954687:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((316726338956179625428095283712690955282431231499115649:ℚ)/1537317478125000000000000000000000000000000000000000000),((936247:ℚ)/2000000)⟩
theorem valid17 : Valid source22 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((8629139803:ℚ)/10000000000),((663409567:ℚ)/625000000),((-1790228701:ℚ)/2025000000),((-81480537833:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((77231332003856324230095280489875998454772810325063129:ℚ)/311391210937500000000000000000000000000000000000000000),((936247:ℚ)/2000000)⟩
theorem valid18 : Valid source22 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((2106622147:ℚ)/2000000000),((3604702671:ℚ)/2500000000),(-1:ℚ),((-20484843617:ℚ)/44160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((318467432184782357697536521:ℚ)/975052800000000000000000000),((936247:ℚ)/2000000)⟩
theorem valid19 : Valid source22 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet19 valid19
private theorem node0_2 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source22 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source22 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source22 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source22 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4291:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source22 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4291:ℚ)/6400) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((4291:ℚ)/6400) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source22 nn0 nn1 Qcell ((4291:ℚ)/6400) ((4329:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source22 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source22 nn0 nn1 Qcell ((4329:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source22 nn0 nn1 Qcell ((4291:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound source22 nn0 nn1 Qcell ((4291:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC05
#check @N11Formalization.C450Source22GroupedC05.bound
#print axioms N11Formalization.C450Source22GroupedC05.valid0
#print axioms N11Formalization.C450Source22GroupedC05.valid1
#print axioms N11Formalization.C450Source22GroupedC05.valid2
#print axioms N11Formalization.C450Source22GroupedC05.valid3
#print axioms N11Formalization.C450Source22GroupedC05.valid4
#print axioms N11Formalization.C450Source22GroupedC05.valid5
#print axioms N11Formalization.C450Source22GroupedC05.valid6
#print axioms N11Formalization.C450Source22GroupedC05.valid7
#print axioms N11Formalization.C450Source22GroupedC05.valid8
#print axioms N11Formalization.C450Source22GroupedC05.valid9
#print axioms N11Formalization.C450Source22GroupedC05.valid10
#print axioms N11Formalization.C450Source22GroupedC05.valid11
#print axioms N11Formalization.C450Source22GroupedC05.valid12
#print axioms N11Formalization.C450Source22GroupedC05.valid13
#print axioms N11Formalization.C450Source22GroupedC05.valid14
#print axioms N11Formalization.C450Source22GroupedC05.valid15
#print axioms N11Formalization.C450Source22GroupedC05.valid16
#print axioms N11Formalization.C450Source22GroupedC05.valid17
#print axioms N11Formalization.C450Source22GroupedC05.valid18
#print axioms N11Formalization.C450Source22GroupedC05.valid19
#print axioms N11Formalization.C450Source22GroupedC05.bound
#print axioms N11Formalization.C450Source22GroupedC05.endpoint_checks
