import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((13:ℚ)/16),((7:ℚ)/8),((2487470599:ℚ)/5000000000),((265942139:ℚ)/500000000),((42897117787:ℚ)/51500000000),((2405594973:ℚ)/2480000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((8571462181:ℚ)/10000000000),((-123904419907027467109858987094005777:ℚ)/392764544000000000000000000000000000),((-1276126405620177122596981:ℚ)/2310400000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((260687079:ℚ)/500000000),((5557996307:ℚ)/10000000000),((1481644009:ℚ)/1780000000),((49785974149:ℚ)/51500000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((8147935349:ℚ)/10000000000),((-95343802625019171968067580682946043652199537996582061789:ℚ)/296791696166992187500000000000000000000000000000000000000),((-503491065502220044225558789:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((2726224359:ℚ)/5000000000),((1135505857:ℚ)/2000000000),((46000916667:ℚ)/54350000000),((10124540999:ℚ)/10680000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7706938797:ℚ)/10000000000),((-957307964029794229388956611623239495524735115533091946171:ℚ)/2758684690800000000000000000000000000000000000000000000000),((-19999087857475534206476989:ℚ)/36966400000000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((2785885203:ℚ)/5000000000),((5797035103:ℚ)/10000000000),((46776507639:ℚ)/55300000000),((51459245721:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1869716957:ℚ)/2500000000),((-12091096199359400845668511610202604142233624517888046688017:ℚ)/34680377107373046875000000000000000000000000000000000000000),((-496440543002549774732666749:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((1422768079:ℚ)/2500000000),((5856778267:ℚ)/10000000000),((23775985027:ℚ)/27887500000),((51877447869:ℚ)/55300000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((7245084367:ℚ)/10000000000),((-121232462839604111149704069732651882210829777633676107226693:ℚ)/336865815256250000000000000000000000000000000000000000000000),((-494663664063074513187522229:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((13:ℚ)/16),((7:ℚ)/8),((1437679043:ℚ)/2500000000),((1479128789:ℚ)/2500000000),((23969827559:ℚ)/28125000000),((568430501:ℚ)/606250000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1781466987:ℚ)/2500000000),((-4517958513351646939427993164625338437404346615386749:ℚ)/12533656311035156250000000000000000000000000000000000),((-30805067473742205571260181:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((13:ℚ)/16),((7:ℚ)/8),((5810355457:ℚ)/10000000000),((5946381297:ℚ)/10000000000),((96654620941:ℚ)/112975000000),((52504669079:ℚ)/56250000000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((175124817:ℚ)/250000000),((-204279059215465641713882678093942765004258693578117574145801:ℚ)/558531188964843750000000000000000000000000000000000000000000),((-491987646853876149331784349:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((2920086711:ℚ)/5000000000),((5976245929:ℚ)/10000000000),((48521127243:ℚ)/56725000000),((52713721503:ℚ)/56487500000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((1388781009:ℚ)/2000000000),((-233870104353186320524451894781285879270566949985816073000667:ℚ)/639015783033969116210937500000000000000000000000000000000000),((-491092786641490053530805901:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((13:ℚ)/16),((7:ℚ)/8),((5869990287:ℚ)/10000000000),((6006109071:ℚ)/10000000000),((32476624577:ℚ)/37975000000),((52922763497:ℚ)/56725000000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((6882368237:ℚ)/10000000000),((-25384297958895161796775424643664398867114896567997786187703:ℚ)/69314053338167968750000000000000000000000000000000000000000),((-490196498595219155058815901:ℚ)/924160000000000000000000000)⟩
theorem valid8 : Valid source35 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source35 nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet source35 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((5899806067:ℚ)/10000000000),((3017985371:ℚ)/5000000000),((97817478871:ℚ)/114400000000),((8855299199:ℚ)/9493750000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((3410184867:ℚ)/5000000000),((-10008987613026390463428634924923936522161105414002123679:ℚ)/27313125301742553710937500000000000000000000000000000000),((-122324695590951807962056501:ℚ)/231040000000000000000000000)⟩
theorem valid9 : Valid source35 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source35 nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((13:ℚ)/16),((7:ℚ)/8),((2964810387:ℚ)/5000000000),((6065830959:ℚ)/10000000000),((49102535031:ℚ)/57437500000),((53340816713:ℚ)/57200000000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((6757896469:ℚ)/10000000000),((-98539772202761030759093155866540417667070672264321863266663:ℚ)/268734623300000000000000000000000000000000000000000000000000),((-1352907583524966872525781:ℚ)/2560000000000000000000000)⟩
theorem valid10 : Valid source35 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet source35 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((5959434423:ℚ)/10000000000),((3047844871:ℚ)/5000000000),((32864215833:ℚ)/38450000000),((26774914097:ℚ)/28718750000),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((26152089:ℚ)/39062500),((-10442259274884583107564700370839484765209266798916744285953:ℚ)/28460528796720504760742187500000000000000000000000000000000),((-121874766018168761958595501:ℚ)/231040000000000000000000000)⟩
theorem valid11 : Valid source35 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source35 nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2307:ℚ)/3200),((4633:ℚ)/6400),((13:ℚ)/16),((7:ℚ)/8),((2994623513:ℚ)/5000000000),((1531386777:ℚ)/2500000000),((49490105669:ℚ)/57912500000),((13439707439:ℚ)/14418750000),((1905827251:ℚ)/2000000000),((1907725537:ℚ)/2000000000),((3080928657:ℚ)/10000000000),((3315735203:ℚ)/5000000000),((-141629016083804649642996892664814065203942153586390366263:ℚ)/385782599395202636718750000000000000000000000000000000000),((-30412316332648914102249069:ℚ)/57760000000000000000000000)⟩
theorem valid12 : Valid source35 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source35 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_of_packet source35 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4633:ℚ)/6400),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((1504764649:ℚ)/2500000000),((3077701537:ℚ)/5000000000),((24841940437:ℚ)/29075000000),((26983910759:ℚ)/28956250000),((9519843613:ℚ)/10000000000),((476456813:ℚ)/500000000),((622285377:ℚ)/2000000000),((6567488397:ℚ)/10000000000),((-162064922186201140844942944214286977347786224334749784717:ℚ)/441191049619029998779296875000000000000000000000000000000),((-121423407274090734230058109:ℚ)/231040000000000000000000000)⟩
theorem valid13 : Valid source35 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source35 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1163:ℚ)/1600),((4671:ℚ)/6400),((13:ℚ)/16),((7:ℚ)/8),((6048869147:ℚ)/10000000000),((3092628829:ℚ)/5000000000),((99755298911:ℚ)/116775000000),((27088401803:ℚ)/29075000000),((148605427:ℚ)/156250000),((4759921809:ℚ)/5000000000),((98156347:ℚ)/312500000),((6502973107:ℚ)/10000000000),((-65932397419864154786565377337589565814419584558998262516693:ℚ)/179386213775317382812500000000000000000000000000000000000000),((-121197191763911925256016101:ℚ)/231040000000000000000000000)⟩
theorem valid14 : Valid source35 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source35 nn0 nn1 Qcell ((1163:ℚ)/1600) ((4671:ℚ)/6400) :=
  cell_of_packet source35 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4671:ℚ)/6400),((469:ℚ)/640),((13:ℚ)/16),((7:ℚ)/8),((607867869:ℚ)/1000000000),((3107555439:ℚ)/5000000000),((10014282297:ℚ)/11725000000),((27192888073:ℚ)/29193750000),((9501845013:ℚ)/10000000000),((9510747333:ℚ)/10000000000),((792422551:ℚ)/2500000000),((6437908141:ℚ)/10000000000),((-8940326678997267973641316756853016483624494516930101360591:ℚ)/24310912445301818847656250000000000000000000000000000000000),((-120970618714427513132988381:ℚ)/231040000000000000000000000)⟩
theorem valid15 : Valid source35 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source35 nn0 nn1 Qcell ((4671:ℚ)/6400) ((469:ℚ)/640) :=
  cell_of_packet source35 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((13:ℚ)/16),((7:ℚ)/8),((6108487239:ℚ)/10000000000),((1561240687:ℚ)/2500000000),((100530334107:ℚ)/117725000000),((13648684809:ℚ)/14656250000),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((6372276287:ℚ)/10000000000),((-8523279324213178172449803900814435369332656228110759883469:ℚ)/23164200195360183715820312500000000000000000000000000000000),((-30185922017387110734543709:ℚ)/57760000000000000000000000)⟩
theorem valid16 : Valid source35 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source35 nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet source35 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((1227658961:ℚ)/2000000000),((6274813287:ℚ)/10000000000),((20183566493:ℚ)/23640000000),((54803693009:ℚ)/58862500000),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((157651487:ℚ)/250000000),((-69333858893050854711973892299750485677869342688933140345919:ℚ)/188331782659725952148437500000000000000000000000000000000000),((-482065598937565978265360109:ℚ)/924160000000000000000000000)⟩
theorem valid17 : Valid source35 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source35 nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((13:ℚ)/16),((7:ℚ)/8),((30840507:ℚ)/50000000),((630466251:ℚ)/1000000000),((506526591:ℚ)/593375000),((5501263757:ℚ)/5910000000),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((6239238721:ℚ)/10000000000),((-751951268513565958436057793825606534837768974499209496317:ℚ)/2041457941743750000000000000000000000000000000000000000000),((-4811550145746623276869461:ℚ)/9241600000000000000000000)⟩
theorem valid18 : Valid source35 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet source35 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((1549476759:ℚ)/2500000000),((6334510433:ℚ)/10000000000),((25423197867:ℚ)/29787500000),((55221573031:ℚ)/59337500000),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((6171794021:ℚ)/10000000000),((-286684243957839985806508166135883210768243097018125465364593:ℚ)/777914385201748657226562500000000000000000000000000000000000),((-480242998894772772249778429:ℚ)/924160000000000000000000000)⟩
theorem valid19 : Valid source35 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source35 nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((2383:ℚ)/3200),((957:ℚ)/1280),((13:ℚ)/16),((7:ℚ)/8),((249108469:ℚ)/400000000),((397772317:ℚ)/625000000),((4083210097:ℚ)/4785000000),((3464406219:ℚ)/3723437500),((75681297:ℚ)/80000000),((2367032267:ℚ)/2500000000),((1650403157:ℚ)/5000000000),((6103704321:ℚ)/10000000000),((-7115318044118546872761319599135936565394858135375285363:ℚ)/19297638988284766674041748046875000000000000000000000000),((-1872381060937596969439429:ℚ)/3610000000000000000000000)⟩
theorem valid20 : Valid source35 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source35 nn0 nn1 Qcell ((2383:ℚ)/3200) ((957:ℚ)/1280) :=
  cell_of_packet source35 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((957:ℚ)/1280),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((6257515477:ℚ)/10000000000),((6394202441:ℚ)/10000000000),((102467701201:ℚ)/120100000000),((55639417087:ℚ)/59812500000),((4726187811:ℚ)/5000000000),((946016213:ℚ)/1000000000),((831186567:ℚ)/2500000000),((1206989483:ℚ)/2000000000),((-658354918717317953538663308231907503967425327573466517207:ℚ)/1784663660842895507812500000000000000000000000000000000000),((-478414672450741120949953741:ℚ)/924160000000000000000000000)⟩
theorem valid21 : Valid source35 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source35 nn0 nn1 Qcell ((957:ℚ)/1280) ((1201:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((1201:ℚ)/1600),((4823:ℚ)/6400),((13:ℚ)/16),((7:ℚ)/8),((196478697:ℚ)/312500000),((3212023279:ℚ)/5000000000),((459174723:ℚ)/538281250),((27924162953:ℚ)/30025000000),((9444767421:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1673989387:ℚ)/5000000000),((5965499853:ℚ)/10000000000),((-43019077515887395239753049292597664989699061080154027028233:ℚ)/116559664168847656250000000000000000000000000000000000000000),((-119374590270391297596692701:ℚ)/231040000000000000000000000)⟩
theorem valid22 : Valid source35 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source35 nn0 nn1 Qcell ((1201:ℚ)/1600) ((4823:ℚ)/6400) :=
  cell_of_packet source35 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((4823:ℚ)/6400),((2421:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((3158560109:ℚ)/5000000000),((1290777887:ℚ)/2000000000),((51621281417:ℚ)/60525000000),((11211445209:ℚ)/12057500000),((4718667711:ℚ)/5000000000),((4722383713:ℚ)/5000000000),((674104879:ℚ)/2000000000),((1473834211:ℚ)/2500000000),((-2448522850198719408256084456749322434470075766338226190789:ℚ)/6631116030905932617187500000000000000000000000000000000000),((-19063224692329915313984509:ℚ)/36966400000000000000000000)⟩
theorem valid23 : Valid source35 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source35 nn0 nn1 Qcell ((4823:ℚ)/6400) ((2421:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((1586730307:ℚ)/2500000000),((1628392883:ℚ)/2500000000),((25907493991:ℚ)/30500000000),((14118750181:ℚ)/15131250000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1456108039:ℚ)/2500000000),((-53592163855437427349766118265954804496299488468993812529:ℚ)/146754613600158691406250000000000000000000000000000000000),((-29671301958574591283714629:ℚ)/57760000000000000000000000)⟩
theorem valid24 : Valid source35 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source35 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source35 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((6406520583:ℚ)/10000000000),((6573248847:ℚ)/10000000000),((104404767579:ℚ)/122950000000),((56892741929:ℚ)/61000000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((1136056957:ℚ)/2000000000),((-318805187632008335662397947781213451265950776579996785855131:ℚ)/872103560937500000000000000000000000000000000000000000000000),((-472895312423189398436523549:ℚ)/924160000000000000000000000)⟩
theorem valid25 : Valid source35 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((129322329:ℚ)/200000000),((6632921491:ℚ)/10000000000),((701196759:ℚ)/826000000),((57310450437:ℚ)/61475000000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((5532813877:ℚ)/10000000000),((-219438503636034671367432899140634104065544750688563249124289:ℚ)/599688445617871093750000000000000000000000000000000000000000),((-471044058530698483109774341:ℚ)/924160000000000000000000000)⟩
theorem valid26 : Valid source35 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source35 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6525708913:ℚ)/10000000000),((6752253193:ℚ)/10000000000),((105954215869:ℚ)/125800000000),((19381924117:ℚ)/20650000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((5381743:ℚ)/10000000),((-12103656220017030052212372485243118854596594085360629673:ℚ)/33805773249053955078125000000000000000000000000000000000),((-1294527252023349776462149:ℚ)/2560000000000000000000000)⟩
theorem valid27 : Valid source35 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source35 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((6644883931:ℚ)/10000000000),((436929067:ℚ)/625000000),((107503491103:ℚ)/129600000000),((3738503469:ℚ)/3931250000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2533746279:ℚ)/5000000000),((-10537813720452202539578723047007761482423852828781824341:ℚ)/30757924360656738281250000000000000000000000000000000000),((-1796156226686058173701429:ℚ)/3610000000000000000000000)⟩
theorem valid28 : Valid source35 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source35 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨((81:ℚ)/100),((343:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((6883196391:ℚ)/10000000000),((1866975719:ℚ)/2500000000),((15800221869:ℚ)/19600000000),((15788830033:ℚ)/16200000000),((57977633:ℚ)/62500000),((2332870371:ℚ)/2500000000),((1913736159:ℚ)/5000000000),((875613229:ℚ)/2000000000),((-8489623856262571094695580073208990865160727165863199099:ℚ)/27125634375000000000000000000000000000000000000000000000),((-27782707820825682636583021:ℚ)/57760000000000000000000000)⟩
theorem valid29 : Valid source35 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((343:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet29 valid29
def packet30 : Packet := ⟨((343:ℚ)/400),((181:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((229990177:ℚ)/312500000),((1986181383:ℚ)/2500000000),((3649872301:ℚ)/4525000000),((16623269681:ℚ)/17150000000),((9252071821:ℚ)/10000000000),((1855284257:ℚ)/2000000000),((1946075537:ℚ)/5000000000),((2521442747:ℚ)/10000000000),((-10390895904234905767026690284171148681626488824119466923:ℚ)/32607155656250000000000000000000000000000000000000000000),((-30486301:ℚ)/64000000)⟩
theorem valid30 : Valid source35 packet30 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf30 :
    CellBound source35 nn0 nn1 Qcell ((343:ℚ)/400) ((181:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet30 valid30
def packet31 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((3918008973:ℚ)/5000000000),((1779569771:ℚ)/2000000000),((61494116649:ℚ)/80000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-1715222285831142701966409:ℚ)/6250000000000000000000000),((-30486301:ℚ)/64000000)⟩
theorem valid31 : Valid source35 packet31 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf31 :
    CellBound source35 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet31 valid31
def packet32 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((549268841:ℚ)/625000000),((2541205763:ℚ)/2000000000),((8460494933:ℚ)/13800000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1514525289029:ℚ)/8625000000000),((-30486301:ℚ)/64000000)⟩
theorem valid32 : Valid source35 packet32 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf32 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet32 valid32
private theorem node0_2 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source35 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source35 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source35 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source35 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source35 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source35 nn0 nn1 Qcell ((2269:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_8 node8_16
private theorem node16_18 :
    CellBound source35 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_join leaf16 leaf17
private theorem node18_20 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_join leaf18 leaf19
private theorem node16_20 :
    CellBound source35 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join node16_18 node18_20
private theorem node20_22 :
    CellBound source35 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join leaf20 leaf21
private theorem node22_24 :
    CellBound source35 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_join leaf22 leaf23
private theorem node20_24 :
    CellBound source35 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join node20_22 node22_24
private theorem node16_24 :
    CellBound source35 nn0 nn1 Qcell ((469:ℚ)/640) ((2421:ℚ)/3200) :=
  cell_join node16_20 node20_24
private theorem node24_26 :
    CellBound source35 nn0 nn1 Qcell ((2421:ℚ)/3200) ((2459:ℚ)/3200) :=
  cell_join leaf24 leaf25
private theorem node26_28 :
    CellBound source35 nn0 nn1 Qcell ((2459:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join leaf26 leaf27
private theorem node24_28 :
    CellBound source35 nn0 nn1 Qcell ((2421:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join node24_26 node26_28
private theorem node28_30 :
    CellBound source35 nn0 nn1 Qcell ((629:ℚ)/800) ((343:ℚ)/400) :=
  cell_join leaf28 leaf29
private theorem node31_33 :
    CellBound source35 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf31 leaf32
private theorem node30_33 :
    CellBound source35 nn0 nn1 Qcell ((343:ℚ)/400) ((69:ℚ)/50) :=
  cell_join leaf30 node31_33
private theorem node28_33 :
    CellBound source35 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node28_30 node30_33
private theorem node24_33 :
    CellBound source35 nn0 nn1 Qcell ((2421:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node24_28 node28_33
private theorem node16_33 :
    CellBound source35 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node16_24 node24_33
private theorem node0_33 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_16 node16_33
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_33
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29,packet30,packet31,packet32]
theorem packet_count : packets.length = 33 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC30
#check @N11Formalization.C450Source35GroupedC30.bound
#print axioms N11Formalization.C450Source35GroupedC30.valid0
#print axioms N11Formalization.C450Source35GroupedC30.valid1
#print axioms N11Formalization.C450Source35GroupedC30.valid2
#print axioms N11Formalization.C450Source35GroupedC30.valid3
#print axioms N11Formalization.C450Source35GroupedC30.valid4
#print axioms N11Formalization.C450Source35GroupedC30.valid5
#print axioms N11Formalization.C450Source35GroupedC30.valid6
#print axioms N11Formalization.C450Source35GroupedC30.valid7
#print axioms N11Formalization.C450Source35GroupedC30.valid8
#print axioms N11Formalization.C450Source35GroupedC30.valid9
#print axioms N11Formalization.C450Source35GroupedC30.valid10
#print axioms N11Formalization.C450Source35GroupedC30.valid11
#print axioms N11Formalization.C450Source35GroupedC30.valid12
#print axioms N11Formalization.C450Source35GroupedC30.valid13
#print axioms N11Formalization.C450Source35GroupedC30.valid14
#print axioms N11Formalization.C450Source35GroupedC30.valid15
#print axioms N11Formalization.C450Source35GroupedC30.valid16
#print axioms N11Formalization.C450Source35GroupedC30.valid17
#print axioms N11Formalization.C450Source35GroupedC30.valid18
#print axioms N11Formalization.C450Source35GroupedC30.valid19
#print axioms N11Formalization.C450Source35GroupedC30.valid20
#print axioms N11Formalization.C450Source35GroupedC30.valid21
#print axioms N11Formalization.C450Source35GroupedC30.valid22
#print axioms N11Formalization.C450Source35GroupedC30.valid23
#print axioms N11Formalization.C450Source35GroupedC30.valid24
#print axioms N11Formalization.C450Source35GroupedC30.valid25
#print axioms N11Formalization.C450Source35GroupedC30.valid26
#print axioms N11Formalization.C450Source35GroupedC30.valid27
#print axioms N11Formalization.C450Source35GroupedC30.valid28
#print axioms N11Formalization.C450Source35GroupedC30.valid29
#print axioms N11Formalization.C450Source35GroupedC30.valid30
#print axioms N11Formalization.C450Source35GroupedC30.valid31
#print axioms N11Formalization.C450Source35GroupedC30.valid32
#print axioms N11Formalization.C450Source35GroupedC30.bound
#print axioms N11Formalization.C450Source35GroupedC30.endpoint_checks
