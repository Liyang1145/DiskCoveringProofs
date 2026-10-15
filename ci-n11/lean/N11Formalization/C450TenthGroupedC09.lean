import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((3166659489:ℚ)/5000000000),((826243257:ℚ)/1250000000),((-746243257:ℚ)/1550000000),((-19286616423:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((732111201:ℚ)/1250000000),((664436144760926283501218149506899286097191836031812821467:ℚ)/26464482031250000000000000000000000000000000000000000000000),((25474625350337872823497:ℚ)/225625000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((3285532857:ℚ)/5000000000),((855964391:ℚ)/1250000000),((-775964391:ℚ)/1609375000),((-6706243333:ℚ)/17800000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1316037249:ℚ)/2500000000),((22717089780868411679427527976511213902712113453279478161:ℚ)/907647587500000000000000000000000000000000000000000000000),((25325234322291872762793:ℚ)/225625000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((3404397433:ℚ)/5000000000),((3483296299:ℚ)/5000000000),((-3163296299:ℚ)/6675000000),((-20950782031:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2301783759:ℚ)/5000000000),((73300171318905818316718563451534421983422195224826715423:ℚ)/3010231647656250000000000000000000000000000000000000000000),((402559429005068969602853:ℚ)/3610000000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((3463826713:ℚ)/5000000000),((3513014837:ℚ)/5000000000),((-3193014837:ℚ)/6793750000),((-1256869823:ℚ)/3225000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((52974853:ℚ)/125000000),((456339340877729771117314273042288734335235853067211833:ℚ)/18989672387695312500000000000000000000000000000000000000),((401239069094050810179557:ℚ)/3610000000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((6987081293:ℚ)/10000000000),((3542732841:ℚ)/5000000000),((-3222732841:ℚ)/6853125000),((-43149569051:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2021820071:ℚ)/5000000000),((6765044174693918142550100231130280519147955789969496773:ℚ)/281571491406250000000000000000000000000000000000000000000),((400647943351708542626493:ℚ)/3610000000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((7046508251:ℚ)/10000000000),((3557591647:ℚ)/5000000000),((-3237591647:ℚ)/6912500000),((-43565557757:ℚ)/111075000000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3840037107:ℚ)/10000000000),((12114972402548369211910136684827468207363608345590272756931:ℚ)/507478138055639648437500000000000000000000000000000000000000),((399988798948461537213677:ℚ)/3610000000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((1769055349:ℚ)/2500000000),((7144900649:ℚ)/10000000000),((-6504900649:ℚ)/13884375000),((-10943387443:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3734293427:ℚ)/10000000000),((898553344850786333161649240538081291683262911498127234259:ℚ)/37641341929026031494140625000000000000000000000000000000000),((1598775860394130045644253:ℚ)/14440000000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((3552967161:ℚ)/5000000000),((7174617751:ℚ)/10000000000),((-6534617751:ℚ)/13943750000),((-21990770127:ℚ)/56012500000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((906404073:ℚ)/2500000000),((2339628833549733686279374882656450891997526983492061909107:ℚ)/98015430042026855468750000000000000000000000000000000000000),((1597597686711905986594653:ℚ)/14440000000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-1:ℚ)/2),((-7:ℚ)/16),((7135647033:ℚ)/10000000000),((3602167301:ℚ)/5000000000),((-3282167301:ℚ)/7001562500),((-14729843077:ℚ)/37500000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((3513733009:ℚ)/10000000000),((413101138325395906205306184795789865150840847290238286389:ℚ)/17307329177856445312500000000000000000000000000000000000000),((399105168635129774364453:ℚ)/3610000000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((716535953:ℚ)/1000000000),((3617025603:ℚ)/5000000000),((-3297025603:ℚ)/7031250000),((-4439751671:ℚ)/11297500000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((339832641:ℚ)/1000000000),((1935841585100532455924606288256743214092033700782805781:ℚ)/81109098948339843750000000000000000000000000000000000000),((398811205959883031386677:ℚ)/3610000000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7195071817:ℚ)/10000000000),((3631883783:ℚ)/5000000000),((-3311883783:ℚ)/7060937500),((-44605502719:ℚ)/113450000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((819755989:ℚ)/2500000000),((2460651372519944246812805763076095755638013048809718548939:ℚ)/103104083948380859375000000000000000000000000000000000000000),((398517533603157746881117:ℚ)/3610000000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((903097987:ℚ)/1250000000),((1458696737:ℚ)/2000000000),((-1330696737:ℚ)/2836250000),((-5601685909:ℚ)/14240625000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((3155383227:ℚ)/10000000000),((46540457844282427131785436874996230120898501012751727799:ℚ)/1950214446807289123535156250000000000000000000000000000000),((63715864246479010001357:ℚ)/577600000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((725449577:ℚ)/1000000000),((3661599783:ℚ)/5000000000),((-3341599783:ℚ)/7120312500),((-346319003:ℚ)/880000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((3026872063:ℚ)/10000000000),((66165477742773715764048221017842640992178200611840627:ℚ)/2772739200000000000000000000000000000000000000000000000),((397931059735296642549117:ℚ)/3610000000000000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7284207441:ℚ)/10000000000),((11812209:ℚ)/16000000),((-10788209:ℚ)/22880000),((-15076484029:ℚ)/38450000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((57856817:ℚ)/200000000),((12991217588883511579724056622746606471279403971507969:ℚ)/541244743377685546875000000000000000000000000000000000),((4072547746845593197:ℚ)/36966400000000000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((3671815093:ℚ)/5000000000),((232564399:ℚ)/312500000),((-425128798:ℚ)/901171875),((-22822705651:ℚ)/58150000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1302387157:ℚ)/5000000000),((68037924726897520631163641970106401909728196291637831250003:ℚ)/2835154751819531250000000000000000000000000000000000000000000),((6205087246967581256387:ℚ)/56406250000000000000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((7403052149:ℚ)/10000000000),((756091839:ℚ)/1000000000),((-692091839:ℚ)/1453750000),((-46061365043:ℚ)/118200000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((91261199:ℚ)/400000000),((2697071847962283771531970301478548857691495187262144704873:ℚ)/111144609987500000000000000000000000000000000000000000000000),((15867548718940831954413:ℚ)/144400000000000000000000)⟩
theorem valid15 : Valid tenth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/2),((-7:ℚ)/16),((7521893809:ℚ)/10000000000),((3899311783:ℚ)/5000000000),((-3579311783:ℚ)/7387500000),((-46893256663:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1434906413:ℚ)/10000000000),((55391039645437503248927120582842485871534106073411400775169:ℚ)/2235762850000000000000000000000000000000000000000000000000000),((1664545351650353:ℚ)/15200000000000000)⟩
theorem valid16 : Valid tenth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((1551913711:ℚ)/2000000000),((8273997779:ℚ)/10000000000),((-7633997779:ℚ)/15250000000),((-9711395977:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((56860489353201803265339040827247225772611066885955342701:ℚ)/2213062041600000000000000000000000000000000000000000000000),((218489:ℚ)/2000000)⟩
theorem valid17 : Valid tenth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((8234887273:ℚ)/10000000000),((10175138821:ℚ)/10000000000),((-1059459869:ℚ)/1800000000),((-51884210911:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((6984797473266897829567931422128893483070314799912422399669:ℚ)/230400000000000000000000000000000000000000000000000000000000),((218489:ℚ)/2000000)⟩
theorem valid18 : Valid tenth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((506792957:ℚ)/500000000),((6988238907:ℚ)/5000000000),((-6668238907:ℚ)/10000000000),((-3259550699:ℚ)/11040000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((220248136458960045027610878264830210892917645093467427:ℚ)/6307372800000000000000000000000000000000000000000000000),((218489:ℚ)/2000000)⟩
theorem valid19 : Valid tenth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet19 valid19
private theorem node0_2 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound tenth nn0 nn1 Qcell ((4481:ℚ)/6400) ((4519:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((4519:ℚ)/6400) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((4519:ℚ)/6400) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((4557:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound tenth nn0 nn1 Qcell ((4557:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC09
#check @N11Formalization.C450TenthGroupedC09.bound
#print axioms N11Formalization.C450TenthGroupedC09.valid0
#print axioms N11Formalization.C450TenthGroupedC09.valid1
#print axioms N11Formalization.C450TenthGroupedC09.valid2
#print axioms N11Formalization.C450TenthGroupedC09.valid3
#print axioms N11Formalization.C450TenthGroupedC09.valid4
#print axioms N11Formalization.C450TenthGroupedC09.valid5
#print axioms N11Formalization.C450TenthGroupedC09.valid6
#print axioms N11Formalization.C450TenthGroupedC09.valid7
#print axioms N11Formalization.C450TenthGroupedC09.valid8
#print axioms N11Formalization.C450TenthGroupedC09.valid9
#print axioms N11Formalization.C450TenthGroupedC09.valid10
#print axioms N11Formalization.C450TenthGroupedC09.valid11
#print axioms N11Formalization.C450TenthGroupedC09.valid12
#print axioms N11Formalization.C450TenthGroupedC09.valid13
#print axioms N11Formalization.C450TenthGroupedC09.valid14
#print axioms N11Formalization.C450TenthGroupedC09.valid15
#print axioms N11Formalization.C450TenthGroupedC09.valid16
#print axioms N11Formalization.C450TenthGroupedC09.valid17
#print axioms N11Formalization.C450TenthGroupedC09.valid18
#print axioms N11Formalization.C450TenthGroupedC09.valid19
#print axioms N11Formalization.C450TenthGroupedC09.bound
#print axioms N11Formalization.C450TenthGroupedC09.endpoint_checks
