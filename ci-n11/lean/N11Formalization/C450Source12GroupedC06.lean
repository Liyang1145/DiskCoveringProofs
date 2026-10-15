import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((3221066051:ℚ)/5000000000),((6732065501:ℚ)/10000000000),((-67652720511:ℚ)/99200000000),((-2869066051:ℚ)/5150000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5592581079:ℚ)/10000000000),((154240683287009830140920498393552963676413446686523105813617:ℚ)/4045474803200000000000000000000000000000000000000000000000000),((16263888231862454802209361:ℚ)/73932800000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((6679922723:ℚ)/10000000000),((6850959387:ℚ)/10000000000),((-68960553257:ℚ)/103000000000),((-5975922723:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2485835531:ℚ)/5000000000),((4277203044548396195473235976286277506157626229509152971487071:ℚ)/117425574563183593750000000000000000000000000000000000000000000),((48770191272309639334353827:ℚ)/221798400000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((6798810123:ℚ)/10000000000),((1393969629:ℚ)/2000000000),((-14053665919:ℚ)/20980000000),((-6094810123:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((57913147:ℚ)/125000000),((780695216783097742153700753545601440505061283383643938371:ℚ)/21429782486083593750000000000000000000000000000000000000000),((1950548130213225463689203:ℚ)/8871936000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-11:ℚ)/16),((-5:ℚ)/8),((6917692627:ℚ)/10000000000),((1405858137:ℚ)/2000000000),((-14184439507:ℚ)/21360000000),((-6213692627:ℚ)/10775000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2134873903:ℚ)/5000000000),((32823099389843206530101967495330862737353323867221117383:ℚ)/920782591938281250000000000000000000000000000000000000000),((1950123742624328229558827:ℚ)/8871936000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((6977132123:ℚ)/10000000000),((7088732043:ℚ)/10000000000),((-71576052473:ℚ)/107750000000),((-6273132123:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((254799097:ℚ)/625000000),((20588346254395221188871251343501394152814417298166412016377199:ℚ)/577392262041497802734375000000000000000000000000000000000000000),((48749939670378166542414467:ℚ)/221798400000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7036570491:ℚ)/10000000000),((7118452289:ℚ)/10000000000),((-71902975179:ℚ)/108700000000),((-6332570491:ℚ)/10917500000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((3874790967:ℚ)/10000000000),((21097471253791443658358114496332835856536094250224275651433653:ℚ)/597991578858436694335937500000000000000000000000000000000000000),((16248222180555401785595081:ℚ)/73932800000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((353314463:ℚ)/500000000),((28592689:ℚ)/40000000),((-288919579:ℚ)/436700000),((-318114463:ℚ)/548250000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((753990839:ℚ)/2000000000),((460072644237181626692669314697286642095394717499751911:ℚ)/13037839419765100488281250000000000000000000000000000000),((259963264605302561961:ℚ)/1182924800000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-11:ℚ)/16),((-5:ℚ)/8),((7096007759:ℚ)/10000000000),((717789193:ℚ)/1000000000),((-7255681123:ℚ)/10965000000),((-6392007759:ℚ)/11012500000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((366226581:ℚ)/1000000000),((130622446846221740696384214602783242435405001961343848967:ℚ)/3700956700396130371093750000000000000000000000000000000000),((162471888926349636092889:ℚ)/739328000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((7125725989:ℚ)/10000000000),((3603805667:ℚ)/5000000000),((-36441862337:ℚ)/55062500000),((-917389427:ℚ)/1580000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((11098331:ℚ)/31250000),((897938251774742133979123697996827216118960556099998059799:ℚ)/25436772857195138931274414062500000000000000000000000000000),((4061669186240419087526929:ℚ)/18483200000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((1431088791:ℚ)/2000000000),((226166577:ℚ)/312500000),((-2287832347:ℚ)/3456250000),((-1290288791:ℚ)/2221500000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((429656639:ℚ)/1250000000),((936719660800943246677007487861020419653788596533666757447:ℚ)/26530587124521517753601074218750000000000000000000000000000),((190384776498857457501053:ℚ)/866400000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((359258083:ℚ)/500000000),((290681973:ℚ)/400000000),((-2941501703:ℚ)/4443000000),((-324058083:ℚ)/557750000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3319274563:ℚ)/10000000000),((13939370478940980095248450091922364849708613215385243987:ℚ)/394733847899790063476562500000000000000000000000000000000),((77979174918590231045507:ℚ)/354877440000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7214879107:ℚ)/10000000000),((7296767919:ℚ)/10000000000),((-73864447109:ℚ)/111550000000),((-6510879107:ℚ)/11202500000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((1598556431:ℚ)/5000000000),((15381234448178621634813100817755551539449951804296771137046923:ℚ)/435490452032504201171875000000000000000000000000000000000000000),((48735474855649256110821563:ℚ)/221798400000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-11:ℚ)/16),((-5:ℚ)/8),((72445963:ℚ)/100000000),((7326486251:ℚ)/10000000000),((-74191348761:ℚ)/112025000000),((-65405963:ℚ)/112500000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((1535134073:ℚ)/5000000000),((2046033729336454028917794996349011307427725075805798461:ℚ)/57920018418002128601074218750000000000000000000000000000),((16244658125976567671303361:ℚ)/73932800000000000000000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((3637156621:ℚ)/5000000000),((3678102161:ℚ)/5000000000),((-37259123771:ℚ)/56250000000),((-3285156621:ℚ)/5648750000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((1469066679:ℚ)/5000000000),((1857812982997836784935842298609650172366637734657380818584031:ℚ)/52583384227752685546875000000000000000000000000000000000000000),((4061040240868590033269481:ℚ)/18483200000000000000000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((456501871:ℚ)/625000000),((7385922137:ℚ)/10000000000),((-74845143507:ℚ)/112975000000),((-412501871:ℚ)/709062500),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((2799959033:ℚ)/10000000000),((256175010793806552201194967441154351035394377850500523998141:ℚ)/7249634058520379623413085937500000000000000000000000000000000),((16243666797631261743175609:ℚ)/73932800000000000000000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((3666873193:ℚ)/5000000000),((7445357011:ℚ)/10000000000),((-75498927121:ℚ)/113450000000),((-3314873193:ℚ)/5720000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2654801661:ℚ)/10000000000),((416480173383657963460865350764506274503188746282925458406207:ℚ)/11663948952536181640625000000000000000000000000000000000000000),((16243923894804221981165681:ℚ)/73932800000000000000000000)⟩
theorem valid15 : Valid source12 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((3696589281:ℚ)/5000000000),((7564223821:ℚ)/10000000000),((-5908189387:ℚ)/8800000000),((-3344589281:ℚ)/5815000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2338276223:ℚ)/10000000000),((1192442279308980119923001094302351706443591160979946644799:ℚ)/32732169800000000000000000000000000000000000000000000000000),((16244473955404005195642801:ℚ)/73932800000000000000000000)⟩
theorem valid16 : Valid source12 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((1878010027:ℚ)/2500000000),((7683086869:ℚ)/10000000000),((-78113955559:ℚ)/116300000000),((-1702010027:ℚ)/2955000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1522896199:ℚ)/10000000000),((217158517949903441051784528850711131358906132386252983678233:ℚ)/5961720890949511718750000000000000000000000000000000000000000),((2811711831813059:ℚ)/12800000000000000)⟩
theorem valid17 : Valid source12 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-11:ℚ)/16),((-5:ℚ)/8),((7630898063:ℚ)/10000000000),((7920802389:ℚ)/10000000000),((-80728826279:ℚ)/118200000000),((-6926898063:ℚ)/12200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((30227769128457540794880667734052887561839579814423960528259:ℚ)/800112176240625000000000000000000000000000000000000000000000),((14055391:ℚ)/64000000)⟩
theorem valid18 : Valid source12 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((245893871:ℚ)/312500000),((4198097733:ℚ)/5000000000),((-42979075063:ℚ)/61000000000),((-223893871:ℚ)/405000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((128029297265794462395885353619665519823576599649583173847:ℚ)/3178838671875000000000000000000000000000000000000000000000),((14055391:ℚ)/64000000)⟩
theorem valid19 : Valid source12 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((8343979241:ℚ)/10000000000),((10297394011:ℚ)/10000000000),((-106871334121:ℚ)/129600000000),((-7639979241:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((15249003572810923984487287304026426664536731330728106941:ℚ)/283435200000000000000000000000000000000000000000000000000),((14055391:ℚ)/64000000)⟩
theorem valid20 : Valid source12 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((10245123809:ℚ)/10000000000),((7049400229:ℚ)/5000000000),((-74343402519:ℚ)/80000000000),((-3180374603:ℚ)/7360000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((286578975354760603236467080988739305139:ℚ)/4232000000000000000000000000000000000000),((14055391:ℚ)/64000000)⟩
theorem valid21 : Valid source12 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet21 valid21
private theorem node0_2 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source12 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source12 nn0 nn1 Qcell ((4367:ℚ)/6400) ((881:ℚ)/1280) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((881:ℚ)/1280) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source12 nn0 nn1 Qcell ((881:ℚ)/1280) ((2231:ℚ)/3200) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_5 node5_11
private theorem node11_13 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf11 leaf12
private theorem node14_16 :
    CellBound source12 nn0 nn1 Qcell ((4519:ℚ)/6400) ((143:ℚ)/200) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf13 node14_16
private theorem node11_16 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join node11_13 node13_16
private theorem node17_19 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf16 node17_19
private theorem node20_22 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf19 node20_22
private theorem node16_22 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node16_19 node19_22
private theorem node11_22 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node11_16 node16_22
private theorem node0_22 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_22
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_22
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21]
theorem packet_count : packets.length = 22 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC06
#check @N11Formalization.C450Source12GroupedC06.bound
#print axioms N11Formalization.C450Source12GroupedC06.valid0
#print axioms N11Formalization.C450Source12GroupedC06.valid1
#print axioms N11Formalization.C450Source12GroupedC06.valid2
#print axioms N11Formalization.C450Source12GroupedC06.valid3
#print axioms N11Formalization.C450Source12GroupedC06.valid4
#print axioms N11Formalization.C450Source12GroupedC06.valid5
#print axioms N11Formalization.C450Source12GroupedC06.valid6
#print axioms N11Formalization.C450Source12GroupedC06.valid7
#print axioms N11Formalization.C450Source12GroupedC06.valid8
#print axioms N11Formalization.C450Source12GroupedC06.valid9
#print axioms N11Formalization.C450Source12GroupedC06.valid10
#print axioms N11Formalization.C450Source12GroupedC06.valid11
#print axioms N11Formalization.C450Source12GroupedC06.valid12
#print axioms N11Formalization.C450Source12GroupedC06.valid13
#print axioms N11Formalization.C450Source12GroupedC06.valid14
#print axioms N11Formalization.C450Source12GroupedC06.valid15
#print axioms N11Formalization.C450Source12GroupedC06.valid16
#print axioms N11Formalization.C450Source12GroupedC06.valid17
#print axioms N11Formalization.C450Source12GroupedC06.valid18
#print axioms N11Formalization.C450Source12GroupedC06.valid19
#print axioms N11Formalization.C450Source12GroupedC06.valid20
#print axioms N11Formalization.C450Source12GroupedC06.valid21
#print axioms N11Formalization.C450Source12GroupedC06.bound
#print axioms N11Formalization.C450Source12GroupedC06.endpoint_checks
