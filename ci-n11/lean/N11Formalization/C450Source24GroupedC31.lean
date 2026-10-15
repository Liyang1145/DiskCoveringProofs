import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((1065845771:ℚ)/2000000000),((5891390623:ℚ)/10000000000),((2956306799:ℚ)/3560000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7936970179:ℚ)/10000000000),((-442660562718039948437786128024085213:ℚ)/1409938000000000000000000000000000000),((-934389875083597330054741:ℚ)/2957312000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((5804818143:ℚ)/10000000000),((6010378979:ℚ)/10000000000),((47673727001:ℚ)/54350000000),((20975136937:ℚ)/21360000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1403257633:ℚ)/2000000000),((-184435519895352614453849268367180646278306579334236312549:ℚ)/501705274609375000000000000000000000000000000000000000000),((-69164001971543432623795447:ℚ)/221798400000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((5923702567:ℚ)/10000000000),((6129359121:ℚ)/10000000000),((48505917969:ℚ)/55300000000),((21332077363:ℚ)/21740000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3385167987:ℚ)/5000000000),((-433066722533024732881655178538830502264220554780010547:ℚ)/1179634326171875000000000000000000000000000000000000000),((-22730232300392718087518189:ℚ)/73932800000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/8),((15:ℚ)/16),((1208516473:ℚ)/2000000000),((1562082867:ℚ)/2500000000),((9867615311:ℚ)/11250000000),((774606943:ℚ)/790000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((651662417:ℚ)/1000000000),((-19118321481541916629672140335695247357161278676534817:ℚ)/52142143249511718750000000000000000000000000000000000),((-896238365180524638960429:ℚ)/2957312000000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((1540364443:ℚ)/2500000000),((6307814841:ℚ)/10000000000),((12542551101:ℚ)/14181250000),((21867444523:ℚ)/22500000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6254185983:ℚ)/10000000000),((-8354950702421018792363660655604715112658140342826441:ℚ)/22280943124771118164062500000000000000000000000000000),((-1390468991302125962686949:ℚ)/4620800000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((6220893897:ℚ)/10000000000),((6367296409:ℚ)/10000000000),((50586257279:ℚ)/57200000000),((22045889227:ℚ)/22690000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1529834519:ℚ)/2500000000),((-219128195794686494637592262280520377147277412790654475611:ℚ)/584841400000000000000000000000000000000000000000000000000),((-66256508174496779058013927:ℚ)/221798400000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((3140164503:ℚ)/5000000000),((3213388109:ℚ)/5000000000),((25501151521:ℚ)/28837500000),((1010196757:ℚ)/1040000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((239274001:ℚ)/400000000),((-3287956653948342142183732564652404718350054557449863:ℚ)/8782216388940811157226562500000000000000000000000000),((-16442656141772453009145127:ℚ)/55449600000000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((1584940781:ℚ)/2500000000),((6486254309:ℚ)/10000000000),((12854585467:ℚ)/14537500000),((22402762927:ℚ)/23070000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((5841532563:ℚ)/10000000000),((-3591820362763020792711543851767064637653537215838278223:ℚ)/9601060467529296875000000000000000000000000000000000000),((-1360101258688512833446261:ℚ)/4620800000000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((7:ℚ)/8),((15:ℚ)/16),((3199598137:ℚ)/5000000000),((3272865363:ℚ)/5000000000),((25917186959:ℚ)/29312500000),((11290596089:ℚ)/11630000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((712271723:ℚ)/1250000000),((-12609911505907171746281381224824379259623000855649591111:ℚ)/33731201934814453125000000000000000000000000000000000000),((-5399934612989273758023469:ℚ)/18483200000000000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((6458628481:ℚ)/10000000000),((6575468319:ℚ)/10000000000),((52250399367:ℚ)/58862500000),((22670404957:ℚ)/23450000000),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((1110307029:ℚ)/2000000000),((-14163952933466779991074844793583478031515843579740415691:ℚ)/37490152813720703125000000000000000000000000000000000000),((-21520714907827231231593661:ℚ)/73932800000000000000000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((6488344237:ℚ)/10000000000),((1651301377:ℚ)/2500000000),((17486136553:ℚ)/19700000000),((334700243:ℚ)/346250000),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1095380573:ℚ)/2000000000),((-2255707240450588458792469514628037241905026837480138213:ℚ)/5972947656250000000000000000000000000000000000000000000),((-21439807558297218126884869:ℚ)/73932800000000000000000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((3259029883:ℚ)/5000000000),((1332935739:ℚ)/2000000000),((26333209181:ℚ)/29787500000),((4587607217:ℚ)/4728000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((5401346547:ℚ)/10000000000),((-92503097204674026282258095122618976973734381810750036483:ℚ)/247784104376220703125000000000000000000000000000000000000),((-5319023432203243733982389:ℚ)/18483200000000000000000000)⟩
theorem valid11 : Valid source24 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((6577490153:ℚ)/10000000000),((268966013:ℚ)/400000000),((53082431071:ℚ)/60050000000),((924658039:ℚ)/953200000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((5247300141:ℚ)/10000000000),((-189343500820748779303807294998508276887194819872867166737:ℚ)/507516679980468750000000000000000000000000000000000000000),((-21114330475121322530228109:ℚ)/73932800000000000000000000)⟩
theorem valid12 : Valid source24 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source24 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((6636919663:ℚ)/10000000000),((1356724087:ℚ)/2000000000),((5944270849:ℚ)/6725000000),((4658972261:ℚ)/4804000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((5089042519:ℚ)/10000000000),((-265776005155916791137089658494752400577969181240208983:ℚ)/712833581542968750000000000000000000000000000000000000),((-20952606488133222689426269:ℚ)/73932800000000000000000000)⟩
theorem valid13 : Valid source24 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source24 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((1339269663:ℚ)/2000000000),((342154453:ℚ)/500000000),((10782887641:ℚ)/12200000000),((1173663359:ℚ)/1210500000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4926164677:ℚ)/10000000000),((-6343310327585709346256563769841045317919246767044887967:ℚ)/17023575000000000000000000000000000000000000000000000000),((-131311084232107611546253:ℚ)/466944000000000000000000)⟩
theorem valid14 : Valid source24 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source24 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source24 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((6755776131:ℚ)/10000000000),((1380511247:ℚ)/2000000000),((54330432917:ℚ)/61475000000),((4730333741:ℚ)/4880000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((2379094469:ℚ)/5000000000),((-16898112935606436143756743047735314746865941350780823753:ℚ)/45375941708374023437500000000000000000000000000000000000),((-61887827770362174992486383:ℚ)/221798400000000000000000000)⟩
theorem valid15 : Valid source24 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((681520313:ℚ)/1000000000),((6962021993:ℚ)/10000000000),((5474642191:ℚ)/6195000000),((23830065979:ℚ)/24590000000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((4584551667:ℚ)/10000000000),((-39504393569855802235416841475823810559450637874458893:ℚ)/106139225390625000000000000000000000000000000000000000),((-204676691561444486850669:ℚ)/739328000000000000000000)⟩
theorem valid16 : Valid source24 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source24 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((687462933:ℚ)/1000000000),((1770237347:ℚ)/2500000000),((5516240531:ℚ)/6290000000),((6046712041:ℚ)/6195000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2202289969:ℚ)/5000000000),((-212480699739136431807352494578316514485966749207969693:ℚ)/583261380468750000000000000000000000000000000000000000),((-604214873841795115333567:ℚ)/2217984000000000000000000)⟩
theorem valid17 : Valid source24 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source24 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((437092463:ℚ)/625000000),((365939427:ℚ)/500000000),((3499647241:ℚ)/4050000000),((1245018281:ℚ)/1258000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((804437739:ℚ)/2000000000),((-2687597307235023827976568127992097640158306435047367:ℚ)/7688671875000000000000000000000000000000000000000000),((-76118350475500843351569:ℚ)/288800000000000000000000)⟩
theorem valid18 : Valid source24 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source24 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((28924683:ℚ)/40000000),((8269966817:ℚ)/10000000000),((230632781:ℚ)/289600000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((3128189717:ℚ)/10000000000),((-3953969556233801906043800165448729784026442787387:ℚ)/14231378400000000000000000000000000000000000000000),((-898555933828552237567:ℚ)/3548774400000000000000)⟩
theorem valid19 : Valid source24 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((8181835587:ℚ)/10000000000),((9220920881:ℚ)/10000000000),((64312849109:ℚ)/80000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-114250229654924054093986089065749232573495286680275939161:ℚ)/400000000000000000000000000000000000000000000000000000000),((-4057109:ℚ)/16000000)⟩
theorem valid20 : Valid source24 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source24 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((2283093499:ℚ)/2500000000),((3255855587:ℚ)/2500000000),((5913884831:ℚ)/9200000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-12710383015137643814551308994384457:ℚ)/97336000000000000000000000000000000),((-4057109:ℚ)/16000000)⟩
theorem valid21 : Valid source24 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet21 valid21
private theorem node0_2 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2269:ℚ)/3200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source24 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source24 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source24 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_5 node5_11
private theorem node11_13 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf11 leaf12
private theorem node14_16 :
    CellBound source24 nn0 nn1 Qcell ((2421:ℚ)/3200) ((2459:ℚ)/3200) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source24 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2459:ℚ)/3200) :=
  cell_join leaf13 node14_16
private theorem node11_16 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((2459:ℚ)/3200) :=
  cell_join node11_13 node13_16
private theorem node17_19 :
    CellBound source24 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source24 nn0 nn1 Qcell ((2459:ℚ)/3200) ((81:ℚ)/100) :=
  cell_join leaf16 node17_19
private theorem node20_22 :
    CellBound source24 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf19 node20_22
private theorem node16_22 :
    CellBound source24 nn0 nn1 Qcell ((2459:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node16_19 node19_22
private theorem node11_22 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_16 node16_22
private theorem node0_22 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_22
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_22
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21]
theorem packet_count : packets.length = 22 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC31
#check @N11Formalization.C450Source24GroupedC31.bound
#print axioms N11Formalization.C450Source24GroupedC31.valid0
#print axioms N11Formalization.C450Source24GroupedC31.valid1
#print axioms N11Formalization.C450Source24GroupedC31.valid2
#print axioms N11Formalization.C450Source24GroupedC31.valid3
#print axioms N11Formalization.C450Source24GroupedC31.valid4
#print axioms N11Formalization.C450Source24GroupedC31.valid5
#print axioms N11Formalization.C450Source24GroupedC31.valid6
#print axioms N11Formalization.C450Source24GroupedC31.valid7
#print axioms N11Formalization.C450Source24GroupedC31.valid8
#print axioms N11Formalization.C450Source24GroupedC31.valid9
#print axioms N11Formalization.C450Source24GroupedC31.valid10
#print axioms N11Formalization.C450Source24GroupedC31.valid11
#print axioms N11Formalization.C450Source24GroupedC31.valid12
#print axioms N11Formalization.C450Source24GroupedC31.valid13
#print axioms N11Formalization.C450Source24GroupedC31.valid14
#print axioms N11Formalization.C450Source24GroupedC31.valid15
#print axioms N11Formalization.C450Source24GroupedC31.valid16
#print axioms N11Formalization.C450Source24GroupedC31.valid17
#print axioms N11Formalization.C450Source24GroupedC31.valid18
#print axioms N11Formalization.C450Source24GroupedC31.valid19
#print axioms N11Formalization.C450Source24GroupedC31.valid20
#print axioms N11Formalization.C450Source24GroupedC31.valid21
#print axioms N11Formalization.C450Source24GroupedC31.bound
#print axioms N11Formalization.C450Source24GroupedC31.endpoint_checks
