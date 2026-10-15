import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((6349043121:ℚ)/10000000000),((6628172857:ℚ)/10000000000),((-5908172857:ℚ)/12400000000),((-38043301847:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1454838627:ℚ)/2500000000),((22464611059750908082489038552956216547581932803626892559019:ℚ)/635147568750000000000000000000000000000000000000000000000000),((44788740908450566314637:ℚ)/380000000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((263474221:ℚ)/400000000),((3433002589:ℚ)/5000000000),((-3073002589:ℚ)/6437500000),((-529439849:ℚ)/1424000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1044530019:ℚ)/2000000000),((16382732345787755575153818992075890795077331758429247:ℚ)/464715564800000000000000000000000000000000000000000000),((211148114701055714844287:ℚ)/1805000000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((6824645657:ℚ)/10000000000),((218278519:ℚ)/312500000),((-195778519:ℚ)/417187500),((-41372519599:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2278198827:ℚ)/5000000000),((73523439098481451915554990963620387711131448893404451093133:ℚ)/2143284933131250000000000000000000000000000000000000000000000),((6543791642912505311611:ℚ)/56406250000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((6943533103:ℚ)/10000000000),((7044364273:ℚ)/10000000000),((-6324364273:ℚ)/13587500000),((-14068243907:ℚ)/36550000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((104672221:ℚ)/250000000),((2807765524662885655106955168841425528091937005323716329021:ℚ)/82930009280664062500000000000000000000000000000000000000000),((834116032171521507313863:ℚ)/7220000000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((7002975037:ℚ)/10000000000),((3551907309:ℚ)/5000000000),((-1063969103:ℚ)/2284375000),((-42620825259:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1995075521:ℚ)/5000000000),((3269095916311513648226488651379893406714890814463055371681:ℚ)/96579021552343750000000000000000000000000000000000000000000),((624399549735393378609821:ℚ)/5415000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((7062415819:ℚ)/10000000000),((7133539307:ℚ)/10000000000),((-916219901:ℚ)/1975000000),((-14345636911:ℚ)/37025000000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((945943697:ℚ)/2500000000),((632179340673939720875985566921902206080031644663886368227:ℚ)/18795486594653320312500000000000000000000000000000000000000),((830790524354227689974703:ℚ)/7220000000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7092135787:ℚ)/10000000000),((3581631839:ℚ)/5000000000),((-3221631839:ℚ)/6942187500),((-43244950509:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1838233381:ℚ)/5000000000),((81021049918806644714496658751615436541780230581243408183023:ℚ)/2409045883457666015625000000000000000000000000000000000000000),((207500145663046530337287:ℚ)/1805000000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((3560927739:ℚ)/5000000000),((899123467:ℚ)/1250000000),((-809123467:ℚ)/1742968750),((-21726494173:ℚ)/56012500000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((1783041497:ℚ)/5000000000),((3296200191639500737714012569983180858033389478408992962043:ℚ)/98015430042026855468750000000000000000000000000000000000000),((12956426877884397129683:ℚ)/112812500000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-1:ℚ)/2),((-7:ℚ)/16),((446973431:ℚ)/625000000),((1444542297:ℚ)/2000000000),((-1300542297:ℚ)/2800625000),((-2728814017:ℚ)/7031250000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((1726163973:ℚ)/5000000000),((3836362185566436411916078655567608541129899710584256179:ℚ)/114086398389190435409545898437500000000000000000000000000),((99410728418897711314469:ℚ)/866400000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((1795323511:ℚ)/2500000000),((453277183:ℚ)/625000000),((-408277183:ℚ)/878906250),((-10967264577:ℚ)/28243750000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((833714027:ℚ)/2500000000),((42613008790303001936028868084789965244699127884282928993:ℚ)/1267329671067810058593750000000000000000000000000000000000),((3232948564337350847233:ℚ)/28203125000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((3605506463:ℚ)/5000000000),((728215807:ℚ)/1000000000),((-656215807:ℚ)/1412187500),((-22038545241:ℚ)/56725000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((3213259311:ℚ)/10000000000),((433316878982463281117612699297695609952629205036232863391:ℚ)/12888010493547607421875000000000000000000000000000000000000),((8268476070021135161703:ℚ)/72200000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((905091443:ℚ)/1250000000),((3655940457:ℚ)/5000000000),((-3295940457:ℚ)/7090625000),((-1845213367:ℚ)/4746875000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((3087049589:ℚ)/10000000000),((50994697032524085309780188088860596006864302578209638563:ℚ)/1516833458627891540527343750000000000000000000000000000000),((619545795263727309856709:ℚ)/5415000000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((3635224951:ℚ)/5000000000),((917700433:ℚ)/1250000000),((-118242919:ℚ)/254296875),((-22246574657:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((2955635467:ℚ)/10000000000),((25597871802348199702445804752113173098253950818739355082043:ℚ)/761463502800000000000000000000000000000000000000000000000000),((12894924881140383687483:ℚ)/112812500000000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((1825042001:ℚ)/2500000000),((462565481:ℚ)/625000000),((-417565481:ℚ)/893750000),((-11175294007:ℚ)/28837500000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1409144193:ℚ)/5000000000),((7720207682240905688063845187004263207301552819480553:ℚ)/228337626112461090087890625000000000000000000000000000),((3221316381646662164717:ℚ)/28203125000000000000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((147192069:ℚ)/200000000),((1865122699:ℚ)/2500000000),((-1685122699:ℚ)/3604687500),((-902344483:ℚ)/2326000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((630469079:ℚ)/2500000000),((6133592477079563207554544851871264403020883031639406561:ℚ)/181449904116450000000000000000000000000000000000000000000),((51443124439245385713247:ℚ)/451250000000000000000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((7419037907:ℚ)/10000000000),((3789686853:ℚ)/5000000000),((-3429686853:ℚ)/7268750000),((-45533265349:ℚ)/118200000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2186590897:ℚ)/10000000000),((3798470603831561065347594505801130089362520451661679617861:ℚ)/111144609987500000000000000000000000000000000000000000000000),((616400292734397028257869:ℚ)/5415000000000000000000000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/2),((-7:ℚ)/16),((150758079:ℚ)/200000000),((3908563543:ℚ)/5000000000),((-3548563543:ℚ)/7387500000),((-927306553:ℚ)/2440000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((127919377:ℚ)/1000000000),((623915933205558093066093172532377115505204919072711429:ℚ)/17886102800000000000000000000000000000000000000000000000),((17224848463463:ℚ)/152000000000000)⟩
theorem valid16 : Valid source11 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((7775625177:ℚ)/10000000000),((1658517841:ℚ)/2000000000),((-1514517841:ℚ)/3050000000),((-48029376239:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((10002974393895683343448687729364908134154387408616751699593:ℚ)/276632755200000000000000000000000000000000000000000000000000),((56523:ℚ)/500000)⟩
theorem valid17 : Valid source11 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((4125514331:ℚ)/5000000000),((10193998201:ℚ)/10000000000),((-9473998201:ℚ)/16200000000),((-25678600317:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((11044992425327414469525885574360557151207400911307800458533:ℚ)/259200000000000000000000000000000000000000000000000000000000),((56523:ℚ)/500000)⟩
theorem valid18 : Valid source11 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((10152258937:ℚ)/10000000000),((13995651491:ℚ)/10000000000),((-13275651491:ℚ)/20000000000),((-21555270853:ℚ)/73600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((91701534241123776570310130034473216515943942073465494671:ℚ)/1868851200000000000000000000000000000000000000000000000000),((56523:ℚ)/500000)⟩
theorem valid19 : Valid source11 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet19 valid19
private theorem node0_2 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source11 nn0 nn1 Qcell ((4481:ℚ)/6400) ((4519:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source11 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((4519:ℚ)/6400) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((4519:ℚ)/6400) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source11 nn0 nn1 Qcell ((4519:ℚ)/6400) ((4557:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source11 nn0 nn1 Qcell ((4557:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source11 nn0 nn1 Qcell ((4519:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound source11 nn0 nn1 Qcell ((4519:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC09
#check @N11Formalization.C450Source11GroupedC09.bound
#print axioms N11Formalization.C450Source11GroupedC09.valid0
#print axioms N11Formalization.C450Source11GroupedC09.valid1
#print axioms N11Formalization.C450Source11GroupedC09.valid2
#print axioms N11Formalization.C450Source11GroupedC09.valid3
#print axioms N11Formalization.C450Source11GroupedC09.valid4
#print axioms N11Formalization.C450Source11GroupedC09.valid5
#print axioms N11Formalization.C450Source11GroupedC09.valid6
#print axioms N11Formalization.C450Source11GroupedC09.valid7
#print axioms N11Formalization.C450Source11GroupedC09.valid8
#print axioms N11Formalization.C450Source11GroupedC09.valid9
#print axioms N11Formalization.C450Source11GroupedC09.valid10
#print axioms N11Formalization.C450Source11GroupedC09.valid11
#print axioms N11Formalization.C450Source11GroupedC09.valid12
#print axioms N11Formalization.C450Source11GroupedC09.valid13
#print axioms N11Formalization.C450Source11GroupedC09.valid14
#print axioms N11Formalization.C450Source11GroupedC09.valid15
#print axioms N11Formalization.C450Source11GroupedC09.valid16
#print axioms N11Formalization.C450Source11GroupedC09.valid17
#print axioms N11Formalization.C450Source11GroupedC09.valid18
#print axioms N11Formalization.C450Source11GroupedC09.valid19
#print axioms N11Formalization.C450Source11GroupedC09.bound
#print axioms N11Formalization.C450Source11GroupedC09.endpoint_checks
