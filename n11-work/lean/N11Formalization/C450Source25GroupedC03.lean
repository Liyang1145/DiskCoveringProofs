import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((2003:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((3462129681:ℚ)/5000000000),((7082097037:ℚ)/10000000000),((-42214679259:ℚ)/49600000000),((-37327685853:ℚ)/50075000000),((398569427:ℚ)/400000000),(1:ℚ),((845998389:ℚ)/10000000000),((4248835099:ℚ)/10000000000),((1371977041725409617843548228659545310620625960706413170237289:ℚ)/4895611294474240000000000000000000000000000000000000000000000),((277107630501074130179825791:ℚ)/369664000000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((2003:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((2003:ℚ)/3200),((1011:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((1396771127:ℚ)/2000000000),((1428326967:ℚ)/2000000000),((-8526288769:ℚ)/10015000000),((-15086024651:ℚ)/20220000000),((9929701407:ℚ)/10000000000),((62276473:ℚ)/62500000),((18538009:ℚ)/156250000),((506801797:ℚ)/1250000000),((599336396610124072068127207978744761404985318442911561508697:ℚ)/2139015515138350781250000000000000000000000000000000000000000),((33328378432290385026780613:ℚ)/44359680000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((2003:ℚ)/3200) ((1011:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1011:ℚ)/1600),((4063:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7043447727:ℚ)/10000000000),((7171402587:ℚ)/10000000000),((-42839818109:ℚ)/50550000000),((-76204820451:ℚ)/101575000000),((4956442379:ℚ)/5000000000),((2482425353:ℚ)/2500000000),((1320924081:ℚ)/10000000000),((154030879:ℚ)/400000000),((306129069566310724813518316802216693454233430597884620673933357:ℚ)/1110595464964436132812500000000000000000000000000000000000000000),((834152934859898844434081773:ℚ)/1108992000000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4063:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4063:ℚ)/6400),((2041:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((3536621121:ℚ)/5000000000),((720116959:ℚ)/1000000000),((-4304818713:ℚ)/5078750000),((-38296074573:ℚ)/51025000000),((247409071:ℚ)/250000000),((9912884763:ℚ)/10000000000),((1440948769:ℚ)/10000000000),((29257999:ℚ)/78125000),((3476801905418968641060343765922964839494303063767638563:ℚ)/12613332534641288757324218750000000000000000000000000000),((2783655118869403439349159:ℚ)/3696640000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((4063:ℚ)/6400) ((2041:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((1420607151:ℚ)/2000000000),((1807733963:ℚ)/2500000000),((-10814137741:ℚ)/12756250000),((-5131964321:ℚ)/6835000000),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((3636354467:ℚ)/10000000000),((1670617042894546178467544082722492778121862742112555794378199:ℚ)/6060746527545383071899414062500000000000000000000000000000000),((17417505488590077330159791:ℚ)/23104000000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4101:ℚ)/6400),((8221:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7132828281:ℚ)/10000000000),((7245818709:ℚ)/10000000000),((-43360730963:ℚ)/51262500000),((-77366767653:ℚ)/102762500000),((4936061823:ℚ)/5000000000),((9880131563:ℚ)/10000000000),((320187229:ℚ)/2000000000),((1762246493:ℚ)/5000000000),((3889701966030530046169023534850642381647541147371902677587062873:ℚ)/14225536991741208316040039062500000000000000000000000000000000000),((836512175088905816990470477:ℚ)/1108992000000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((4101:ℚ)/6400) ((8221:ℚ)/12800) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((8221:ℚ)/12800),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((3573862089:ℚ)/5000000000),((3630350693:ℚ)/5000000000),((-21732454851:ℚ)/25690625000),((-38780207157:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((9872123651:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((1733634419:ℚ)/5000000000),((307423210227668556088309964568016128850864179747461789430249:ℚ)/1124290332818479347229003906250000000000000000000000000000000),((69748676552952286312668111:ℚ)/92416000000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((8221:ℚ)/12800) ((103:ℚ)/160) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((103:ℚ)/160),((8259:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7162619833:ℚ)/10000000000),((3637791941:ℚ)/5000000000),((-21784543587:ℚ)/25750000000),((-77754057829:ℚ)/103237500000),((9856320801:ℚ)/10000000000),((616511681:ℚ)/625000000),((1697201141:ℚ)/10000000000),((1704562323:ℚ)/5000000000),((663458611941642159321835378629603067072749457339737969595698211:ℚ)/2426305010022363281250000000000000000000000000000000000000000000),((69788007838234079159481359:ℚ)/92416000000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((8259:ℚ)/12800) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((8259:ℚ)/12800),((4139:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((448594703:ℚ)/625000000),((36452331:ℚ)/50000000),((-218366317:ℚ)/258093750),((-4871731139:ℚ)/6467187500),((984852489:ℚ)/1000000000),((4928160403:ℚ)/5000000000),((1742751127:ℚ)/10000000000),((335001243:ℚ)/1000000000),((2516817868971001202823457396904310596436730493657146049:ℚ)/9203930653910942324638366699218750000000000000000000000),((20948202536320741199437:ℚ)/27724800000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((8259:ℚ)/12800) ((4139:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4139:ℚ)/6400),((8297:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((899051303:ℚ)/1250000000),((365267417:ℚ)/500000000),((-2188871919:ℚ)/2586875000),((-9767666939:ℚ)/12964062500),((9840798677:ℚ)/10000000000),((1969704979:ℚ)/2000000000),((1786759881:ℚ)/10000000000),((3289879939:ℚ)/10000000000),((2036745369500850009137479558201363770077484009235223186525269:ℚ)/7448151960995975297546386718750000000000000000000000000000000),((698666784013449860286071:ℚ)/924160000000000000000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((4139:ℚ)/6400) ((8297:ℚ)/12800) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8297:ℚ)/12800),((2079:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((1801826341:ℚ)/2500000000),((228757197:ℚ)/312500000),((-2742600758:ℚ)/3241015625),((-19583742433:ℚ)/25987500000),((4916570841:ℚ)/5000000000),((4920399341:ℚ)/5000000000),((1829340989:ℚ)/10000000000),((645734017:ℚ)/2000000000),((285142203841469519546321799847887434652951049086484429039:ℚ)/1042710592063045687973499298095703125000000000000000000000),((819211144737142999629853:ℚ)/1083000000000000000000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((8297:ℚ)/12800) ((2079:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2079:ℚ)/3200),((1667:ℚ)/2560),((-7:ℚ)/8),((-13:ℚ)/16),((7222200069:ℚ)/10000000000),((3667556047:ℚ)/5000000000),((-21992892329:ℚ)/25987500000),((-78528600897:ℚ)/104187500000),((4912776717:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((935297099:ℚ)/5000000000),((1583160157:ℚ)/5000000000),((20839711818049113634989025717702771457113647192164697993236939:ℚ)/76205222015831515502929687500000000000000000000000000000000000),((69945359641585717502556551:ℚ)/92416000000000000000000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1667:ℚ)/2560) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1667:ℚ)/2560),((4177:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((361854727:ℚ)/500000000),((734999371:ℚ)/1000000000),((-4408995597:ℚ)/5209375000),((-3936111451:ℚ)/5221250000),((4909016731:ℚ)/5000000000),((9825553439:ℚ)/10000000000),((382121547:ℚ)/2000000000),((387845229:ℚ)/1250000000),((1053954422636083088169611380169690594121906374165231491699847:ℚ)/3853947915681878423690795898437500000000000000000000000000000),((2799388170931343490215599:ℚ)/3696640000000000000000000)⟩
theorem valid12 : Valid source25 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source25 nn0 nn1 Qcell ((1667:ℚ)/2560) ((4177:ℚ)/6400) :=
  cell_of_packet source25 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4177:ℚ)/6400),((8373:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((362599439:ℚ)/500000000),((7364875153:ℚ)/10000000000),((-44194126071:ℚ)/52212500000),((-3945792707:ℚ)/5233125000),((4905290651:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((194946007:ℚ)/1000000000),((94934959:ℚ)/312500000),((4264129947056425661969294058052463272218851295624018619129027189:ℚ)/15592138120369134695434570312500000000000000000000000000000000000),((280096206327456108295857351:ℚ)/369664000000000000000000000)⟩
theorem valid13 : Valid source25 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source25 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8373:ℚ)/12800) :=
  cell_of_packet source25 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((8373:ℚ)/12800),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((7266882789:ℚ)/10000000000),((295190257:ℚ)/400000000),((-590643933:ℚ)/697750000),((-79109476257:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((9810581307:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((742926679:ℚ)/2500000000),((159736373822754593865338489626511027281459689220961186623:ℚ)/584077582494337670898437500000000000000000000000000000000),((448405770064041368034311:ℚ)/591462400000000000000000)⟩
theorem valid14 : Valid source25 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source25 nn0 nn1 Qcell ((8373:ℚ)/12800) ((1049:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-7:ℚ)/8),((-13:ℚ)/16),((7281776569:ℚ)/10000000000),((7409518459:ℚ)/10000000000),((-44506629213:ℚ)/52450000000),((-79303095397:ℚ)/105375000000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((726008051:ℚ)/2500000000),((1766491408091642402101794487631227696659687050860582949359703:ℚ)/6408725116337507812500000000000000000000000000000000000000000),((280568438429918080361302159:ℚ)/369664000000000000000000000)⟩
theorem valid15 : Valid source25 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source25 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source25 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((146231269:ℚ)/200000000),((3719639911:ℚ)/5000000000),((-22357479377:ℚ)/26343750000),((-1593806497:ℚ)/2117000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((690965797:ℚ)/2500000000),((15683668896600780333183209273588323856607042945949358349141323:ℚ)/56899966782330894470214843750000000000000000000000000000000000),((70220828403794312784662519:ℚ)/92416000000000000000000000)⟩
theorem valid16 : Valid source25 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source25 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source25 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((3670674717:ℚ)/5000000000),((749880057:ℚ)/1000000000),((-4513160399:ℚ)/5292500000),((-13346257107:ℚ)/17800000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((654100347:ℚ)/2500000000),((7034069400970690521653360351803675307142588552796133293:ℚ)/25133894006372070312500000000000000000000000000000000000),((8445395804360328839335333:ℚ)/11089920000000000000000000)⟩
theorem valid17 : Valid source25 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source25 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((3700459381:ℚ)/5000000000),((1904458599:ℚ)/2500000000),((-11491210193:ℚ)/13350000000),((-40425971953:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2293907913:ℚ)/10000000000),((562481895646068995125964406780469502657893744170549378988267:ℚ)/1952272303971093750000000000000000000000000000000000000000000),((97847853:ℚ)/128000000)⟩
theorem valid18 : Valid source25 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((3760023589:ℚ)/5000000000),((1934214609:ℚ)/2500000000),((-11699502263:ℚ)/13587500000),((-41200306657:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1451799267:ℚ)/10000000000),((440042782484775343236002526733441417853894122789414912733:ℚ)/1528878231854057312011718750000000000000000000000000000000),((97847853:ℚ)/128000000)⟩
theorem valid19 : Valid source25 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((7639162533:ℚ)/10000000000),((7974879119:ℚ)/10000000000),((-48464153833:ℚ)/55300000000),((-7631737539:ℚ)/10400000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((7740392843977492767030192066231103871910460095937630538909:ℚ)/25517849743750000000000000000000000000000000000000000000000),((97847853:ℚ)/128000000)⟩
theorem valid20 : Valid source25 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((1969339169:ℚ)/2500000000),((8926655677:ℚ)/10000000000),((-4240506903:ℚ)/4400000000),((-21761409197:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((114244597313936172092162700006312610446836801240599293031:ℚ)/291089700000000000000000000000000000000000000000000000000),((97847853:ℚ)/128000000)⟩
theorem valid21 : Valid source25 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((8829724707:ℚ)/10000000000),((4939029211:ℚ)/5000000000),((-30893204477:ℚ)/32400000000),((-99426421191:ℚ)/144800000000),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),(0:ℚ),((163762528030019857438830679400897442769430711856256911993023:ℚ)/435263465025000000000000000000000000000000000000000000000000),((97847853:ℚ)/128000000)⟩
theorem valid22 : Valid source25 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((97815941:ℚ)/100000000),((2707298541:ℚ)/2500000000),((-17111089787:ℚ)/18100000000),((-1118007233:ℚ)/1600000000),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((3380224586229804020006336650335270388627602530271852793:ℚ)/9265220312500000000000000000000000000000000000000000000),((97847853:ℚ)/128000000)⟩
theorem valid23 : Valid source25 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source25 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((10733107453:ℚ)/10000000000),((2926434339:ℚ)/2000000000),(-1:ℚ),((-124170396889:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((719768835798211318040667229:ℚ)/1523520000000000000000000000),((97847853:ℚ)/128000000)⟩
theorem valid24 : Valid source25 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet24 valid24
private theorem node1_3 :
    CellBound source25 nn0 nn1 Qcell ((2003:ℚ)/3200) ((4063:ℚ)/6400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((4063:ℚ)/6400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source25 nn0 nn1 Qcell ((2041:ℚ)/3200) ((8221:ℚ)/12800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source25 nn0 nn1 Qcell ((4063:ℚ)/6400) ((8221:ℚ)/12800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((8221:ℚ)/12800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source25 nn0 nn1 Qcell ((8221:ℚ)/12800) ((4139:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source25 nn0 nn1 Qcell ((8297:ℚ)/12800) ((1667:ℚ)/2560) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source25 nn0 nn1 Qcell ((4139:ℚ)/6400) ((1667:ℚ)/2560) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source25 nn0 nn1 Qcell ((8221:ℚ)/12800) ((1667:ℚ)/2560) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((1667:ℚ)/2560) :=
  cell_join node0_6 node6_12
private theorem node13_15 :
    CellBound source25 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source25 nn0 nn1 Qcell ((1667:ℚ)/2560) ((1049:ℚ)/1600) :=
  cell_join leaf12 node13_15
private theorem node16_18 :
    CellBound source25 nn0 nn1 Qcell ((843:ℚ)/1280) ((267:ℚ)/400) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source25 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf15 node16_18
private theorem node12_18 :
    CellBound source25 nn0 nn1 Qcell ((1667:ℚ)/2560) ((267:ℚ)/400) :=
  cell_join node12_15 node15_18
private theorem node19_21 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf18 node19_21
private theorem node21_23 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((181:ℚ)/200) :=
  cell_join leaf21 leaf22
private theorem node23_25 :
    CellBound source25 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf23 leaf24
private theorem node21_25 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node21_23 node23_25
private theorem node18_25 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node18_21 node21_25
private theorem node12_25 :
    CellBound source25 nn0 nn1 Qcell ((1667:ℚ)/2560) ((69:ℚ)/50) :=
  cell_join node12_18 node18_25
private theorem node0_25 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_12 node12_25
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_25
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24]
theorem packet_count : packets.length = 25 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC03
#check @N11Formalization.C450Source25GroupedC03.bound
#print axioms N11Formalization.C450Source25GroupedC03.valid0
#print axioms N11Formalization.C450Source25GroupedC03.valid1
#print axioms N11Formalization.C450Source25GroupedC03.valid2
#print axioms N11Formalization.C450Source25GroupedC03.valid3
#print axioms N11Formalization.C450Source25GroupedC03.valid4
#print axioms N11Formalization.C450Source25GroupedC03.valid5
#print axioms N11Formalization.C450Source25GroupedC03.valid6
#print axioms N11Formalization.C450Source25GroupedC03.valid7
#print axioms N11Formalization.C450Source25GroupedC03.valid8
#print axioms N11Formalization.C450Source25GroupedC03.valid9
#print axioms N11Formalization.C450Source25GroupedC03.valid10
#print axioms N11Formalization.C450Source25GroupedC03.valid11
#print axioms N11Formalization.C450Source25GroupedC03.valid12
#print axioms N11Formalization.C450Source25GroupedC03.valid13
#print axioms N11Formalization.C450Source25GroupedC03.valid14
#print axioms N11Formalization.C450Source25GroupedC03.valid15
#print axioms N11Formalization.C450Source25GroupedC03.valid16
#print axioms N11Formalization.C450Source25GroupedC03.valid17
#print axioms N11Formalization.C450Source25GroupedC03.valid18
#print axioms N11Formalization.C450Source25GroupedC03.valid19
#print axioms N11Formalization.C450Source25GroupedC03.valid20
#print axioms N11Formalization.C450Source25GroupedC03.valid21
#print axioms N11Formalization.C450Source25GroupedC03.valid22
#print axioms N11Formalization.C450Source25GroupedC03.valid23
#print axioms N11Formalization.C450Source25GroupedC03.valid24
#print axioms N11Formalization.C450Source25GroupedC03.bound
#print axioms N11Formalization.C450Source25GroupedC03.endpoint_checks
