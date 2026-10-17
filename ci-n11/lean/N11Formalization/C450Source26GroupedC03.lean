import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((2003:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((6954690273:ℚ)/10000000000),((3557812501:ℚ)/5000000000),((-21064687507:ℚ)/24800000000),((-74410973549:ℚ)/100150000000),((398569427:ℚ)/400000000),(1:ℚ),((845998389:ℚ)/10000000000),((1037658073:ℚ)/2500000000),((180640161147234235785127570235475809154621690305656258613907:ℚ)/611951411809280000000000000000000000000000000000000000000000),((7277753023834228293711061:ℚ)/9241600000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((2003:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((2003:ℚ)/3200),((1011:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((280572253:ℚ)/400000000),((7175176711:ℚ)/10000000000),((-42546236977:ℚ)/50075000000),((-1002479763:ℚ)/1348000000),((9929701407:ℚ)/10000000000),((62276473:ℚ)/62500000),((18538009:ℚ)/156250000),((493949807:ℚ)/1250000000),((78928607115770760257972402254087862753474824648805108377251371:ℚ)/267376939392293847656250000000000000000000000000000000000000000),((29175367441435872095484781:ℚ)/36966400000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((2003:ℚ)/3200) ((1011:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1011:ℚ)/1600),((4063:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((353695891:ℚ)/500000000),((7204951321:ℚ)/10000000000),((-42754659247:ℚ)/50550000000),((-3798046583:ℚ)/5078750000),((4956442379:ℚ)/5000000000),((2482425353:ℚ)/2500000000),((1320924081:ℚ)/10000000000),((3742593117:ℚ)/10000000000),((967768786229686782406778964735365252453101122002471252254177103:ℚ)/3331786394893308398437500000000000000000000000000000000000000000),((29207551024255744537123501:ℚ)/36966400000000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4063:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4063:ℚ)/6400),((2041:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((7103721899:ℚ)/10000000000),((1808681279:ℚ)/2500000000),((-10740768953:ℚ)/12696875000),((-76348384687:ℚ)/102050000000),((247409071:ℚ)/250000000),((9912884763:ℚ)/10000000000),((1440948769:ℚ)/10000000000),((908453821:ℚ)/2500000000),((114504722937619550641274286455179611580939027332515847749:ℚ)/394166641707540273666381835937500000000000000000000000000),((1827483660140022797202301:ℚ)/2310400000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((4063:ℚ)/6400) ((2041:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7133524887:ℚ)/10000000000),((1816124527:ℚ)/2500000000),((-10792871689:ℚ)/12756250000),((-76735823531:ℚ)/102525000000),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((1760918387:ℚ)/5000000000),((1760829321818892530520766829256418292585539590423681898191129:ℚ)/6060746527545383071899414062500000000000000000000000000000000),((1829495629248022335341469:ℚ)/2310400000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4101:ℚ)/6400),((8221:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7163326797:ℚ)/10000000000),((3639692153:ℚ)/5000000000),((-21637845071:ℚ)/25631250000),((-77123248361:ℚ)/102762500000),((4936061823:ℚ)/5000000000),((9880131563:ℚ)/10000000000),((320187229:ℚ)/2000000000),((3406341369:ℚ)/10000000000),((1537586563465465487261694167597624046574890017229997289393093533:ℚ)/5334576371902953118515014648437500000000000000000000000000000000),((7322006827998300458723949:ℚ)/9241600000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((4101:ℚ)/6400) ((8221:ℚ)/12800) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((8221:ℚ)/12800),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((3589113677:ℚ)/5000000000),((1823567577:ℚ)/2500000000),((-10844973039:ℚ)/12845312500),((-38658477801:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((9872123651:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((669432261:ℚ)/2000000000),((324079777702645479913752522557673896029034798787629471104497:ℚ)/1124290332818479347229003906250000000000000000000000000000000),((5494523541177127209552007:ℚ)/6931200000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((8221:ℚ)/12800) ((103:ℚ)/160) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((103:ℚ)/160),((8259:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7193127647:ℚ)/10000000000),((3654578057:ℚ)/5000000000),((-21742046399:ℚ)/25750000000),((-77510659411:ℚ)/103237500000),((9856320801:ℚ)/10000000000),((616511681:ℚ)/625000000),((1697201141:ℚ)/10000000000),((205434859:ℚ)/625000000),((233147617016302237431570762920476316765169740891990497483928119:ℚ)/808768336674121093750000000000000000000000000000000000000000000),((7330056197693759212274189:ℚ)/9241600000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((8259:ℚ)/12800) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((8259:ℚ)/12800),((4139:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7208027679:ℚ)/10000000000),((7324041727:ℚ)/10000000000),((-43588292089:ℚ)/51618750000),((-77704359827:ℚ)/103475000000),((984852489:ℚ)/1000000000),((4928160403:ℚ)/5000000000),((1742751127:ℚ)/10000000000),((32256733:ℚ)/100000000),((127366252862413821186955810337620578922620229547774840821210283:ℚ)/441788671387725231582641601562500000000000000000000000000000000),((29336325028681440816438269:ℚ)/36966400000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((8259:ℚ)/12800) ((4139:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4139:ℚ)/6400),((8297:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((144458549:ℚ)/200000000),((7338927147:ℚ)/10000000000),((-43692490029:ℚ)/51737500000),((-1557961137:ℚ)/2074250000),((9840798677:ℚ)/10000000000),((1969704979:ℚ)/2000000000),((1786759881:ℚ)/10000000000),((1581622539:ℚ)/5000000000),((17179512819445385584773802792045230339090663855500068003343446661:ℚ)/59585215687967802380371093750000000000000000000000000000000000000),((88057278799850616270280447:ℚ)/110899200000000000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((4139:ℚ)/6400) ((8297:ℚ)/12800) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8297:ℚ)/12800),((2079:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((1809456741:ℚ)/2500000000),((919226547:ℚ)/1250000000),((-5474585829:ℚ)/6482031250),((-19522937633:ℚ)/25987500000),((4916570841:ℚ)/5000000000),((4920399341:ℚ)/5000000000),((1829340989:ℚ)/10000000000),((3099603881:ℚ)/10000000000),((16836671980100029358009284549570627285649251525305217562509:ℚ)/58391793155530558526515960693359375000000000000000000000000),((1376649773751464696079247:ℚ)/1732800000000000000000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((8297:ℚ)/12800) ((2079:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7252726221:ℚ)/10000000000),((1476716453:ℚ)/2000000000),((-8801015171:ℚ)/10395000000),((-78285440873:ℚ)/104425000000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((1517336663:ℚ)/5000000000),((73553703496006516049228396478713698485484464877562781263411:ℚ)/253067915139748242187500000000000000000000000000000000000000),((1176029439897542349397749:ℚ)/1478656000000000000000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((3641261987:ℚ)/5000000000),((1482670281:ℚ)/2000000000),((-8842691967:ℚ)/10442500000),((-39336405831:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((362574467:ℚ)/1250000000),((569105251090142721156827219277498962985147771897374384988503:ℚ)/1957872715602696118164062500000000000000000000000000000000000),((3531953701492376332157863:ℚ)/4435968000000000000000000)⟩
theorem valid12 : Valid source26 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source26 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-7:ℚ)/8),((-13:ℚ)/16),((7312320723:ℚ)/10000000000),((3721559903:ℚ)/5000000000),((-22210919321:ℚ)/26225000000),((-79060169399:ℚ)/105375000000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((2760209381:ℚ)/10000000000),((232878377737496759703674997869987895683029157559225165503321:ℚ)/801090639542188476562500000000000000000000000000000000000000),((7366290765537401505957949:ℚ)/9241600000000000000000000)⟩
theorem valid13 : Valid source26 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source26 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source26 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((3671058241:ℚ)/5000000000),((3736443739:ℚ)/5000000000),((-22315106173:ℚ)/26343750000),((-39723757133:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((163281043:ℚ)/625000000),((49627095985119485158325739159451837848836399086836751326482159:ℚ)/170699900346992683410644531250000000000000000000000000000000000),((7374345664260608447963381:ℚ)/9241600000000000000000000)⟩
theorem valid14 : Valid source26 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source26 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((230372227:ℚ)/312500000),((3766210337:ℚ)/5000000000),((-22523472359:ℚ)/26462500000),((-2494838951:ℚ)/3337500000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((2456135409:ℚ)/10000000000),((8347088118036379104770080051322361434905070279660181958903:ℚ)/28275630757168579101562500000000000000000000000000000000000),((7390458505793692853051709:ℚ)/9241600000000000000000000)⟩
theorem valid15 : Valid source26 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source26 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((7431497949:ℚ)/10000000000),((7651478739:ℚ)/10000000000),((-15293450391:ℚ)/17800000000),((-80609473337:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1054839759:ℚ)/5000000000),((12659265719377888443832369007733565189379804493503055456545951:ℚ)/41648475818050000000000000000000000000000000000000000000000000),((51307167:ℚ)/64000000)⟩
theorem valid16 : Valid source26 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((3775330081:ℚ)/5000000000),((7770526179:ℚ)/10000000000),((-46713683253:ℚ)/54350000000),((-41079291053:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((570049151:ℚ)/5000000000),((208043876474460684720006617893515548092081451400377878274619:ℚ)/684937447870617675781250000000000000000000000000000000000000),((51307167:ℚ)/64000000)⟩
theorem valid17 : Valid source26 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((7669808141:ℚ)/10000000000),((4004295657:ℚ)/5000000000),((-24190069599:ℚ)/27650000000),((-83707505833:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((123592803066699168015549117802960984666683744655667656161817:ℚ)/385957477374218750000000000000000000000000000000000000000000),((51307167:ℚ)/64000000)⟩
theorem valid18 : Valid source26 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((7908064251:ℚ)/10000000000),((4480259733:ℚ)/5000000000),((-27521818131:ℚ)/28600000000),((-86804835263:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((3025212957210017109177721690637766957862068980060418462227:ℚ)/7267318987500000000000000000000000000000000000000000000000),((51307167:ℚ)/64000000)⟩
theorem valid19 : Valid source26 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((553790221:ℚ)/625000000),((5431637189:ℚ)/5000000000),(-1:ℚ),((-6199272873:ℚ)/10000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((174051785473034593861720351758528007:ℚ)/375000000000000000000000000000000000),((51307167:ℚ)/64000000)⟩
theorem valid20 : Valid source26 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((2691081929:ℚ)/2500000000),((733325277:ℚ)/500000000),(-1:ℚ),((-30984065077:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((761176074483470464217348039:ℚ)/1523520000000000000000000000),((51307167:ℚ)/64000000)⟩
theorem valid21 : Valid source26 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet21 valid21
private theorem node0_2 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source26 nn0 nn1 Qcell ((4063:ℚ)/6400) ((4101:ℚ)/6400) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source26 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4101:ℚ)/6400) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((4101:ℚ)/6400) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source26 nn0 nn1 Qcell ((8221:ℚ)/12800) ((8259:ℚ)/12800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source26 nn0 nn1 Qcell ((4101:ℚ)/6400) ((8259:ℚ)/12800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source26 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source26 nn0 nn1 Qcell ((8259:ℚ)/12800) ((2079:ℚ)/3200) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source26 nn0 nn1 Qcell ((4101:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join node0_5 node5_11
private theorem node11_13 :
    CellBound source26 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf11 leaf12
private theorem node14_16 :
    CellBound source26 nn0 nn1 Qcell ((843:ℚ)/1280) ((267:ℚ)/400) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source26 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf13 node14_16
private theorem node11_16 :
    CellBound source26 nn0 nn1 Qcell ((2079:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join node11_13 node13_16
private theorem node17_19 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf16 node17_19
private theorem node20_22 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf19 node20_22
private theorem node16_22 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node16_19 node19_22
private theorem node11_22 :
    CellBound source26 nn0 nn1 Qcell ((2079:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node11_16 node16_22
private theorem node0_22 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_22
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_22
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21]
theorem packet_count : packets.length = 22 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC03
#check @N11Formalization.C450Source26GroupedC03.bound
#print axioms N11Formalization.C450Source26GroupedC03.valid0
#print axioms N11Formalization.C450Source26GroupedC03.valid1
#print axioms N11Formalization.C450Source26GroupedC03.valid2
#print axioms N11Formalization.C450Source26GroupedC03.valid3
#print axioms N11Formalization.C450Source26GroupedC03.valid4
#print axioms N11Formalization.C450Source26GroupedC03.valid5
#print axioms N11Formalization.C450Source26GroupedC03.valid6
#print axioms N11Formalization.C450Source26GroupedC03.valid7
#print axioms N11Formalization.C450Source26GroupedC03.valid8
#print axioms N11Formalization.C450Source26GroupedC03.valid9
#print axioms N11Formalization.C450Source26GroupedC03.valid10
#print axioms N11Formalization.C450Source26GroupedC03.valid11
#print axioms N11Formalization.C450Source26GroupedC03.valid12
#print axioms N11Formalization.C450Source26GroupedC03.valid13
#print axioms N11Formalization.C450Source26GroupedC03.valid14
#print axioms N11Formalization.C450Source26GroupedC03.valid15
#print axioms N11Formalization.C450Source26GroupedC03.valid16
#print axioms N11Formalization.C450Source26GroupedC03.valid17
#print axioms N11Formalization.C450Source26GroupedC03.valid18
#print axioms N11Formalization.C450Source26GroupedC03.valid19
#print axioms N11Formalization.C450Source26GroupedC03.valid20
#print axioms N11Formalization.C450Source26GroupedC03.valid21
#print axioms N11Formalization.C450Source26GroupedC03.bound
#print axioms N11Formalization.C450Source26GroupedC03.endpoint_checks
