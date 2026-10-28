import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((1324894327:ℚ)/2000000000),((1704275371:ℚ)/2500000000),((-15867029081:ℚ)/24800000000),((-1081694327:ℚ)/2022000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((320159943:ℚ)/625000000),((3712505006461846567556112176231558332176261897289634807501071:ℚ)/48720010737600000000000000000000000000000000000000000000000000),((226976528363548843938839367:ℚ)/591462400000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((1685925831:ℚ)/2500000000),((1734074651:ℚ)/2500000000),((-16194821161:ℚ)/25275000000),((-1381925831:ℚ)/2575000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((2396376029:ℚ)/5000000000),((122577676122517618761875404495931820711975777994279682122333:ℚ)/1605902664196142578125000000000000000000000000000000000000000),((1061971983537437744287062709:ℚ)/2772480000000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((3431458569:ℚ)/5000000000),((6995891001:ℚ)/10000000000),((-65434801011:ℚ)/103000000000),((-2823458569:ℚ)/5197500000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((4440587993:ℚ)/10000000000),((274723010197877189923227174468570674883806641662286111723875589:ℚ)/3689866750942968750000000000000000000000000000000000000000000000),((4239866407884820751943479509:ℚ)/11089920000000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((138450353:ℚ)/200000000),((7055479439:ℚ)/10000000000),((-66090273829:ℚ)/103950000000),((-114130353:ℚ)/209800000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((2127195617:ℚ)/5000000000),((71970707800049825801296833201799561342205793773763443007724739:ℚ)/965638310981898339843750000000000000000000000000000000000000000),((2259103096170812776238007:ℚ)/5914624000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((1396422811:ℚ)/2000000000),((284602561:ℚ)/400000000),((-2669828171:ℚ)/4196000000),((-1153222811:ℚ)/2117000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((2030110157:ℚ)/5000000000),((1057428147324629400237810329342123488559168837113775635557:ℚ)/14173441520811400000000000000000000000000000000000000000000),((225693083002023507480627583:ℚ)/591462400000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((220053327:ℚ)/312500000),((3572427453:ℚ)/5000000000),((-33536701983:ℚ)/52925000000),((-182053327:ℚ)/332265625),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((385686683:ℚ)/1000000000),((617692937064525169450301007485810395263788656151413282737496137:ℚ)/8379601911990454931640625000000000000000000000000000000000000000),((16514247688812571877552101:ℚ)/43320000000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((1767875301:ℚ)/2500000000),((7174644863:ℚ)/10000000000),((-67401093493:ℚ)/106325000000),((-1463875301:ℚ)/2670000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((937820319:ℚ)/2500000000),((4937473791266009010793624813570202201529828915939170880879667:ℚ)/66945089612122229003906250000000000000000000000000000000000000),((1056397280373803358363225469:ℚ)/2772480000000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((887661873:ℚ)/1250000000),((1801108477:ℚ)/2500000000),((-16932193247:ℚ)/26700000000),((-735661873:ℚ)/1340937500),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((29142311:ℚ)/80000000),((1262810067349429919260527067418734896571548232936527786582017:ℚ)/17112791573291162109375000000000000000000000000000000000000000),((263970288068900839976196901:ℚ)/693120000000000000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-11:ℚ)/16),((-5:ℚ)/8),((7131087819:ℚ)/10000000000),((3617111027:ℚ)/5000000000),((-4861174471:ℚ)/7662500000),((-5915087819:ℚ)/10775000000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3531121133:ℚ)/10000000000),((225964369572311096913336389968049541063421558983016106827:ℚ)/3060534743293547630310058593750000000000000000000000000000),((16885815482886626289858260509:ℚ)/44359680000000000000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7160879719:ℚ)/10000000000),((7264009311:ℚ)/10000000000),((-68384102421:ℚ)/107750000000),((-660542191:ℚ)/1202500000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((853991523:ℚ)/2500000000),((4175751396765992981960285133475835585785958397593594208902131:ℚ)/56529094423678588867187500000000000000000000000000000000000000),((5625835875004530916603224103:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((7190670699:ℚ)/10000000000),((1823448923:ℚ)/2500000000),((-17177938153:ℚ)/27056250000),((-5974670699:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3296957761:ℚ)/10000000000),((48692949895172823311211989686674415227556118580986810579657:ℚ)/658853626180290985107421875000000000000000000000000000000000),((16869174860957863771575477469:ℚ)/44359680000000000000000000000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7220460769:ℚ)/10000000000),((915447651:ℚ)/1250000000),((-8629924161:ℚ)/13587500000),((-6004460769:ℚ)/10917500000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((396707761:ℚ)/1250000000),((690878150086167647097807627136393347492162249881441192452671:ℚ)/9343618419663073348999023437500000000000000000000000000000000),((15568621597637001023161023:ℚ)/40960000000000000000000000)⟩
theorem valid11 : Valid source20 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source20 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7250249943:ℚ)/10000000000),((7353365871:ℚ)/10000000000),((-69367024581:ℚ)/109175000000),((-354955879:ℚ)/645000000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((304555777:ℚ)/1000000000),((1251495841901366495872196537699709828610609658315962823714419:ℚ)/16917611703847448730468750000000000000000000000000000000000000),((16852434611222918939175900181:ℚ)/44359680000000000000000000000)⟩
theorem valid12 : Valid source20 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source20 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((7280038231:ℚ)/10000000000),((7412932681:ℚ)/10000000000),((-70022259491:ℚ)/109650000000),((-6064038231:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2912009607:ℚ)/10000000000),((4424892511027550652172620672852365061325102345050140782980167:ℚ)/59056468487148065185546875000000000000000000000000000000000000),((5614675707782531573596503303:ℚ)/14786560000000000000000000000)⟩
theorem valid13 : Valid source20 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source20 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-11:ℚ)/16),((-5:ℚ)/8),((1834903049:ℚ)/2500000000),((7532056537:ℚ)/10000000000),((-71332621907:ℚ)/110600000000),((-1530903049:ℚ)/2812500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2625223913:ℚ)/10000000000),((102711730916691100945802739784841540808061669960903463117:ℚ)/1337705325878906250000000000000000000000000000000000000000),((350565362846655864418225223:ℚ)/924160000000000000000000000)⟩
theorem valid14 : Valid source20 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source20 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((3729374999:ℚ)/5000000000),((3825583959:ℚ)/5000000000),((-12107141183:ℚ)/18750000000),((-3121374999:ℚ)/5720000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((482744549:ℚ)/2500000000),((32367897250165219304705445864262600741777322316559795775177:ℚ)/421236419677734375000000000000000000000000000000000000000000),((1399421587517509897752358023:ℚ)/3696640000000000000000000000)⟩
theorem valid15 : Valid source20 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((947234357:ℚ)/1250000000),((4301838023:ℚ)/5000000000),((-41560218253:ℚ)/57200000000),((-88359373:ℚ)/180000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),((763232179:ℚ)/10000000000),((121571692035917180538170396196773544750275185837743068317:ℚ)/1214670600000000000000000000000000000000000000000000000000),((87284281410286527536671327:ℚ)/231040000000000000000000000)⟩
theorem valid16 : Valid source20 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((8530476469:ℚ)/10000000000),((105072587:ℚ)/100000000),((-1040598457:ℚ)/1296000000),((-7314476469:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2441769750577968202888962250544578700655928605849901:ℚ)/20407334400000000000000000000000000000000000000000000),((386706701:ℚ)/1024000000)⟩
theorem valid17 : Valid source20 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((1304274063:ℚ)/1250000000),((14311459581:ℚ)/10000000000),((-145906055391:ℚ)/160000000000),((-1152274063:ℚ)/2760000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((380843693396864297969574545377753554674027:ℚ)/2437632000000000000000000000000000000000000),((386706701:ℚ)/1024000000)⟩
theorem valid18 : Valid source20 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source20 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4253:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source20 nn0 nn1 Qcell ((4253:ℚ)/6400) ((431:ℚ)/640) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source20 nn0 nn1 Qcell ((1049:ℚ)/1600) ((431:ℚ)/640) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source20 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source20 nn0 nn1 Qcell ((4367:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source20 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source20 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source20 nn0 nn1 Qcell ((431:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC06
#check @N11Formalization.C450Source20GroupedC06.bound
#print axioms N11Formalization.C450Source20GroupedC06.valid0
#print axioms N11Formalization.C450Source20GroupedC06.valid1
#print axioms N11Formalization.C450Source20GroupedC06.valid2
#print axioms N11Formalization.C450Source20GroupedC06.valid3
#print axioms N11Formalization.C450Source20GroupedC06.valid4
#print axioms N11Formalization.C450Source20GroupedC06.valid5
#print axioms N11Formalization.C450Source20GroupedC06.valid6
#print axioms N11Formalization.C450Source20GroupedC06.valid7
#print axioms N11Formalization.C450Source20GroupedC06.valid8
#print axioms N11Formalization.C450Source20GroupedC06.valid9
#print axioms N11Formalization.C450Source20GroupedC06.valid10
#print axioms N11Formalization.C450Source20GroupedC06.valid11
#print axioms N11Formalization.C450Source20GroupedC06.valid12
#print axioms N11Formalization.C450Source20GroupedC06.valid13
#print axioms N11Formalization.C450Source20GroupedC06.valid14
#print axioms N11Formalization.C450Source20GroupedC06.valid15
#print axioms N11Formalization.C450Source20GroupedC06.valid16
#print axioms N11Formalization.C450Source20GroupedC06.valid17
#print axioms N11Formalization.C450Source20GroupedC06.valid18
#print axioms N11Formalization.C450Source20GroupedC06.bound
#print axioms N11Formalization.C450Source20GroupedC06.endpoint_checks
