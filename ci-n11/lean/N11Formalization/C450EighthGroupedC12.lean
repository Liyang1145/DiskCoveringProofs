import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((1563910907:ℚ)/2500000000),((1303900599:ℚ)/2000000000),((-1150300599:ℚ)/3968000000),((-1283910907:ℚ)/6437500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6039285887:ℚ)/10000000000),((2392010290715143195229481519391626158019531113075515913:ℚ)/155065324401855468750000000000000000000000000000000000000),((16066236880926749396997923:ℚ)/354877440000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((811663057:ℚ)/1250000000),((337859937:ℚ)/500000000),((-299459937:ℚ)/1030000000),((-671663057:ℚ)/3337500000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5464356071:ℚ)/10000000000),((91685915379947919134942050880598727830671800802549113:ℚ)/5983028530883789062500000000000000000000000000000000000),((989637691016261365900787:ℚ)/22179840000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((6730953827:ℚ)/10000000000),((3438020737:ℚ)/5000000000),((-3054020737:ℚ)/10680000000),((-5610953827:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1207251163:ℚ)/2500000000),((167694452136186097249832704520049654387127284803338817189:ℚ)/11162942360058593750000000000000000000000000000000000000000),((32460331375705225910474129:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((6849774593:ℚ)/10000000000),((3497440509:ℚ)/5000000000),((-3113440509:ℚ)/10870000000),((-5729774593:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4480671787:ℚ)/10000000000),((100897156661209806733481426852425535904942329129203421411:ℚ)/6731878190881347656250000000000000000000000000000000000000),((96662048755069346578604363:ℚ)/2217984000000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((3484296463:ℚ)/5000000000),((1410859929:ℚ)/2000000000),((-1257259929:ℚ)/4424000000),((-2924296463:ℚ)/13943750000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((4105032119:ℚ)/10000000000),((8698261985980050063464413768584374823934802183048943393:ℚ)/585630826208400726318359375000000000000000000000000000000),((15339654233147183473821443:ℚ)/354877440000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((3514000609:ℚ)/5000000000),((1422743507:ℚ)/2000000000),((-1269143507:ℚ)/4462000000),((-2954000609:ℚ)/14062500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3904523099:ℚ)/10000000000),((6742992347296045882064874302583646147824948096255186779:ℚ)/454410631209611892700195312500000000000000000000000000000),((5094128214975597860329209:ℚ)/118292480000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-5:ℚ)/16),((-1:ℚ)/4),((1771852237:ℚ)/2500000000),((7143426209:ℚ)/10000000000),((-6375426209:ℚ)/22500000000),((-1491852237:ℚ)/7060937500),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((461716549:ℚ)/1250000000),((97524704420260629327047310364932812045696260933050637:ℚ)/6600675370144844055175781250000000000000000000000000000),((126827789941108908130784721:ℚ)/2957312000000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((7117112607:ℚ)/10000000000),((1434626941:ℚ)/2000000000),((-1281026941:ℚ)/4519000000),((-5997112607:ℚ)/28362500000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((3583916733:ℚ)/10000000000),((23792601363676356676464232612002748357633069631232752391:ℚ)/1611001311693450927734375000000000000000000000000000000000),((5063587155872731651562521:ℚ)/118292480000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-5:ℚ)/16),((-1:ℚ)/4),((714681613:ℚ)/1000000000),((3601421513:ℚ)/5000000000),((-3217421513:ℚ)/11345000000),((-200893871:ℚ)/949375000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((694156619:ℚ)/2000000000),((179141912339749532078358207893097451568932731937968917:ℚ)/12134667669023132324218750000000000000000000000000000000),((31587943045296713349900129:ℚ)/739328000000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((7176519519:ℚ)/10000000000),((3616275587:ℚ)/5000000000),((-3232275587:ℚ)/11392500000),((-6056519519:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((838498803:ℚ)/2500000000),((3277419037960059836715717901761874732736585921741820845887:ℚ)/222093521650000000000000000000000000000000000000000000000000),((31528517443655779328021529:ℚ)/739328000000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((-5:ℚ)/16),((-1:ℚ)/4),((900777847:ℚ)/1250000000),((453891197:ℚ)/625000000),((-405891197:ℚ)/1430000000),((-760777847:ℚ)/3589843750),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((1616578287:ℚ)/5000000000),((914871780970058423411857583292510713668574684975295103:ℚ)/62020312773250043392181396484375000000000000000000000000),((491705358043996969881369:ℚ)/11552000000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((7235925903:ℚ)/10000000000),((91149587:ℚ)/125000000),((-81549587:ℚ)/287187500),((-6115925903:ℚ)/28837500000),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1553897073:ℚ)/5000000000),((238017842601316645417496614975874773533895523639013637:ℚ)/16141713722873210906982421875000000000000000000000000000),((19631137158169745237529:ℚ)/462080000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((7265628901:ℚ)/10000000000),((3675691039:ℚ)/5000000000),((-3291691039:ℚ)/11535000000),((-6145628901:ℚ)/29075000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((372166997:ℚ)/1250000000),((1747022714119565549096706822025544758226950092014994842547:ℚ)/118131447992480468750000000000000000000000000000000000000000),((31363098164799199972398161:ℚ)/739328000000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-5:ℚ)/16),((-1:ℚ)/4),((7325034517:ℚ)/10000000000),((3705398273:ℚ)/5000000000),((-3321398273:ℚ)/11630000000),((-6205034517:ℚ)/29312500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1349073013:ℚ)/5000000000),((2705318520647396671664632636700294013171880505981042416497:ℚ)/183070476634216308593750000000000000000000000000000000000000),((31244808057739993101855889:ℚ)/739328000000000000000000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((1846109909:ℚ)/2500000000),((7470210379:ℚ)/10000000000),((-6702210379:ℚ)/23450000000),((-1566109909:ℚ)/7387500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2387396401:ℚ)/10000000000),((1454268327729013827015273041083110532838018212892444669:ℚ)/98483640847778320312500000000000000000000000000000000000),((124506888662735515660803081:ℚ)/2957312000000000000000000000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((7443844271:ℚ)/10000000000),((7589036199:ℚ)/10000000000),((-2273678733:ℚ)/7880000000),((-6323844271:ℚ)/30025000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1015321537:ℚ)/5000000000),((371164570153471673482341112236989056454868900627493584367:ℚ)/24995196489038085937500000000000000000000000000000000000000),((372416447717870722770600323:ℚ)/8871936000000000000000000000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((7562652133:ℚ)/10000000000),((963482457:ℚ)/1250000000),((-867482457:ℚ)/3002500000),((-6442652133:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((15496697:ℚ)/156250000),((3157884219060995436230183236564183195437789893531904496699:ℚ)/212972016406250000000000000000000000000000000000000000000000),((10115926951932817:ℚ)/243200000000000000)⟩
theorem valid16 : Valid eighth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((7681458191:ℚ)/10000000000),((8183131927:ℚ)/10000000000),((-7415131927:ℚ)/24400000000),((-6561458191:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((66226681179196585961525114932246888143386084935638609239:ℚ)/4322386800000000000000000000000000000000000000000000000000),((42468383:ℚ)/1024000000)⟩
theorem valid17 : Valid eighth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((4078332989:ℚ)/5000000000),((10083962189:ℚ)/10000000000),((-9315962189:ℚ)/25920000000),((-3518332989:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((22819412601091223096698382002428154238158541907986835721:ℚ)/1350000000000000000000000000000000000000000000000000000000),((42468383:ℚ)/1024000000)⟩
theorem valid18 : Valid eighth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((10057299633:ℚ)/10000000000),((2776987317:ℚ)/2000000000),((-2623387317:ℚ)/6400000000),((-8937299633:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((14962259208484643394866665514653457321240007709533006997:ℚ)/788421600000000000000000000000000000000000000000000000000),((42468383:ℚ)/1024000000)⟩
theorem valid19 : Valid eighth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet19 valid19
private theorem node0_2 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((2231:ℚ)/3200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound eighth nn0 nn1 Qcell ((4519:ℚ)/6400) ((143:ℚ)/200) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC12
#check @N11Formalization.C450EighthGroupedC12.bound
#print axioms N11Formalization.C450EighthGroupedC12.valid0
#print axioms N11Formalization.C450EighthGroupedC12.valid1
#print axioms N11Formalization.C450EighthGroupedC12.valid2
#print axioms N11Formalization.C450EighthGroupedC12.valid3
#print axioms N11Formalization.C450EighthGroupedC12.valid4
#print axioms N11Formalization.C450EighthGroupedC12.valid5
#print axioms N11Formalization.C450EighthGroupedC12.valid6
#print axioms N11Formalization.C450EighthGroupedC12.valid7
#print axioms N11Formalization.C450EighthGroupedC12.valid8
#print axioms N11Formalization.C450EighthGroupedC12.valid9
#print axioms N11Formalization.C450EighthGroupedC12.valid10
#print axioms N11Formalization.C450EighthGroupedC12.valid11
#print axioms N11Formalization.C450EighthGroupedC12.valid12
#print axioms N11Formalization.C450EighthGroupedC12.valid13
#print axioms N11Formalization.C450EighthGroupedC12.valid14
#print axioms N11Formalization.C450EighthGroupedC12.valid15
#print axioms N11Formalization.C450EighthGroupedC12.valid16
#print axioms N11Formalization.C450EighthGroupedC12.valid17
#print axioms N11Formalization.C450EighthGroupedC12.valid18
#print axioms N11Formalization.C450EighthGroupedC12.valid19
#print axioms N11Formalization.C450EighthGroupedC12.bound
#print axioms N11Formalization.C450EighthGroupedC12.endpoint_checks
