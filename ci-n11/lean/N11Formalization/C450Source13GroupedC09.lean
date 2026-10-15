import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((3189931311:ℚ)/5000000000),((6664064623:ℚ)/10000000000),((-5784064623:ℚ)/12400000000),((-18489519177:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5745156543:ℚ)/10000000000),((239285679853365001025176136338719779655668351737312052887:ℚ)/5292896406250000000000000000000000000000000000000000000000),((489119218497122176495223:ℚ)/3610000000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((1654457439:ℚ)/2500000000),((3391529233:ℚ)/5000000000),((-2951529233:ℚ)/6437500000),((-9661202073:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((642545123:ℚ)/1250000000),((25483951587908005628893572246324143759177259378406604791:ℚ)/580542123276367187500000000000000000000000000000000000000),((120956400255127702941143:ℚ)/902500000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((1347360119:ℚ)/2000000000),((862755451:ℚ)/1250000000),((-752755451:ℚ)/1639062500),((-7895520833:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4812410889:ℚ)/10000000000),((140119122720776654347122498410071218591642710009290354457:ℚ)/3194693917920000000000000000000000000000000000000000000000),((15039098175161223147399:ℚ)/112812500000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((1713940889:ℚ)/2500000000),((348076653:ℚ)/500000000),((-304076653:ℚ)/667500000),((-10077586223:ℚ)/26937500000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4462447543:ℚ)/10000000000),((367476958077106256230703877525612230269242343170482807:ℚ)/8494384526014328002929687500000000000000000000000000000),((1196517374890995744583:ℚ)/9025000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((6915242213:ℚ)/10000000000),((3510510253:ℚ)/5000000000),((-3070510253:ℚ)/6734375000),((-40726695491:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((427752691:ℚ)/1000000000),((29927953654947673283925755919948939793411347696994787442989:ℚ)/691951914741250000000000000000000000000000000000000000000000),((119330351992155973663783:ℚ)/902500000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((6974719053:ℚ)/10000000000),((7080505997:ℚ)/10000000000),((-6200505997:ℚ)/13587500000),((-13714344457:ℚ)/36550000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((102119659:ℚ)/250000000),((717211464825705698560323326003786877577247681326916234719:ℚ)/16586001856132812500000000000000000000000000000000000000000),((476036520798262995368783:ℚ)/3610000000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((1758548531:ℚ)/2500000000),((3569994793:ℚ)/5000000000),((-3129994793:ℚ)/6853125000),((-10389839717:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3883057711:ℚ)/10000000000),((13048007545504276532893551085161412697265608613603365023:ℚ)/301809442351074218750000000000000000000000000000000000000),((118688071838651811317863:ℚ)/902500000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((7093667471:ℚ)/10000000000),((3584865341:ℚ)/5000000000),((-3144865341:ℚ)/6912500000),((-41975672297:ℚ)/111075000000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((734171077:ℚ)/2000000000),((30517093287591137453889505747045823764372509289092221265043:ℚ)/710469393277895507812500000000000000000000000000000000000000),((118357881806666455651447:ℚ)/902500000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7123403513:ℚ)/10000000000),((179986783:ℚ)/250000000),((-52662261:ℚ)/115703125),((-42183824591:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3560243699:ℚ)/10000000000),((6897997996676483366023171358585257659973527044025849047151:ℚ)/160603058897177734375000000000000000000000000000000000000000),((590987284923939823361:ℚ)/4512500000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((357656957:ℚ)/500000000),((3614605753:ℚ)/5000000000),((-3174605753:ℚ)/6971875000),((-2119598699:ℚ)/5601250000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((3446240879:ℚ)/10000000000),((841909260452445914542495977190076464370041925199059069:ℚ)/19603086008405371093750000000000000000000000000000000000),((118037072865389438139783:ℚ)/902500000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-1:ℚ)/2),((-7:ℚ)/16),((7182874357:ℚ)/10000000000),((3629475623:ℚ)/5000000000),((-3189475623:ℚ)/7001562500),((-42600120499:ℚ)/112500000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((1664248977:ℚ)/5000000000),((4013621126656777650469024562911081708423437336545400772513:ℚ)/93459577560424804687500000000000000000000000000000000000000),((117876729420073504592223:ℚ)/902500000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((7212609171:ℚ)/10000000000),((3644345273:ℚ)/5000000000),((-1068115091:ℚ)/2343750000),((-42808264197:ℚ)/112975000000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((160330119:ℚ)/500000000),((232200272639652707623764173507879882506110291305246128079:ℚ)/5407273263222656250000000000000000000000000000000000000000),((117716426609058785799023:ℚ)/902500000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((3621171793:ℚ)/5000000000),((7318429411:ℚ)/10000000000),((-6438429411:ℚ)/14121875000),((-21508202551:ℚ)/56725000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((385007573:ℚ)/1250000000),((110680791971180893628157762198947780956796910523659837569:ℚ)/2577602098709521484375000000000000000000000000000000000000),((470224657637596988202127:ℚ)/3610000000000000000000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((909009701:ℚ)/1250000000),((3688952929:ℚ)/5000000000),((-3248952929:ℚ)/7090625000),((-5403067907:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2948273759:ℚ)/10000000000),((358262400863968660227740320903158229875622594991745554863:ℚ)/8293782103750000000000000000000000000000000000000000000000),((117405467637164033076567:ℚ)/902500000000000000000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7331544489:ℚ)/10000000000),((743738063:ℚ)/1000000000),((-655738063:ℚ)/1430000000),((-14546937141:ℚ)/38450000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1332910883:ℚ)/5000000000),((1558344965844328141763171716878334305248380419467633:ℚ)/36082982891845703125000000000000000000000000000000000),((4683408908054389676303:ℚ)/36100000000000000000000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((7391009853:ℚ)/10000000000),((7496853767:ℚ)/10000000000),((-6616853767:ℚ)/14418750000),((-44057068971:ℚ)/116300000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2350560181:ℚ)/10000000000),((195871704626143589655127116425007297430658485377504690470137:ℚ)/4536247602911250000000000000000000000000000000000000000000000),((467060559044037929355143:ℚ)/3610000000000000000000000)⟩
theorem valid15 : Valid source13 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source13 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((3725236869:ℚ)/5000000000),((7615795299:ℚ)/10000000000),((-6735795299:ℚ)/14537500000),((-7412219361:ℚ)/19700000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((79477017:ℚ)/400000000),((121333602165576801689436870946981166744950357485912200227:ℚ)/2778615249687500000000000000000000000000000000000000000000),((980712555493637:ℚ)/7600000000000000)⟩
theorem valid16 : Valid source13 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/2),((-7:ℚ)/16),((7569397211:ℚ)/10000000000),((7853660423:ℚ)/10000000000),((-6973660423:ℚ)/14775000000),((-45305780477:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((448853431:ℚ)/5000000000),((19938771722265238443249370617262981679897428353830583681249:ℚ)/447152570000000000000000000000000000000000000000000000000000),((1949993354298203:ℚ)/15200000000000000)⟩
theorem valid17 : Valid source13 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((1561445583:ℚ)/2000000000),((8329326303:ℚ)/10000000000),((-7449326303:ℚ)/15250000000),((-1043791009:ℚ)/2880000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((28083629156143395346439123390945439092202178131276407:ℚ)/607150080000000000000000000000000000000000000000000000),((256191:ℚ)/2000000)⟩
theorem valid18 : Valid source13 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((1035353879:ℚ)/1250000000),((10231356267:ℚ)/10000000000),((-9351356267:ℚ)/16200000000),((-6287477153:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((44238002683356863291027826749769775072736598196326393073:ℚ)/810000000000000000000000000000000000000000000000000000000),((256191:ℚ)/2000000)⟩
theorem valid19 : Valid source13 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((636541859:ℚ)/625000000),((877108607:ℚ)/625000000),((-822108607:ℚ)/1250000000),((-3975793013:ℚ)/13800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((155319953613092778752368888926005716265123611108853359:ℚ)/2463817500000000000000000000000000000000000000000000000),((256191:ℚ)/2000000)⟩
theorem valid20 : Valid source13 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source13 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source13 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source13 nn0 nn1 Qcell ((4443:ℚ)/6400) ((4481:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((4481:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source13 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4481:ℚ)/6400) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((4481:ℚ)/6400) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source13 nn0 nn1 Qcell ((4481:ℚ)/6400) ((4519:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source13 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source13 nn0 nn1 Qcell ((4481:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source13 nn0 nn1 Qcell ((2307:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound source13 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound source13 nn0 nn1 Qcell ((4481:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC09
#check @N11Formalization.C450Source13GroupedC09.bound
#print axioms N11Formalization.C450Source13GroupedC09.valid0
#print axioms N11Formalization.C450Source13GroupedC09.valid1
#print axioms N11Formalization.C450Source13GroupedC09.valid2
#print axioms N11Formalization.C450Source13GroupedC09.valid3
#print axioms N11Formalization.C450Source13GroupedC09.valid4
#print axioms N11Formalization.C450Source13GroupedC09.valid5
#print axioms N11Formalization.C450Source13GroupedC09.valid6
#print axioms N11Formalization.C450Source13GroupedC09.valid7
#print axioms N11Formalization.C450Source13GroupedC09.valid8
#print axioms N11Formalization.C450Source13GroupedC09.valid9
#print axioms N11Formalization.C450Source13GroupedC09.valid10
#print axioms N11Formalization.C450Source13GroupedC09.valid11
#print axioms N11Formalization.C450Source13GroupedC09.valid12
#print axioms N11Formalization.C450Source13GroupedC09.valid13
#print axioms N11Formalization.C450Source13GroupedC09.valid14
#print axioms N11Formalization.C450Source13GroupedC09.valid15
#print axioms N11Formalization.C450Source13GroupedC09.valid16
#print axioms N11Formalization.C450Source13GroupedC09.valid17
#print axioms N11Formalization.C450Source13GroupedC09.valid18
#print axioms N11Formalization.C450Source13GroupedC09.valid19
#print axioms N11Formalization.C450Source13GroupedC09.valid20
#print axioms N11Formalization.C450Source13GroupedC09.bound
#print axioms N11Formalization.C450Source13GroupedC09.endpoint_checks
