import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((6771978593:ℚ)/10000000000),((218105627:ℚ)/312500000),((-544316881:ℚ)/775000000),((-59771764523:ℚ)/101100000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2355717667:ℚ)/5000000000),((349850303702974169940024307006210469024878132922086890901:ℚ)/1486816733935546875000000000000000000000000000000000000000),((4453458071898064015621837:ℚ)/9241600000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((6891352403:ℚ)/10000000000),((7039029733:ℚ)/10000000000),((-17597089199:ℚ)/25275000000),((-61084876433:ℚ)/102050000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((4352684191:ℚ)/10000000000),((30162829635580899286804993495664731874422304944065887999011:ℚ)/131367985831433441162109375000000000000000000000000000000000),((4446465858544848272149717:ℚ)/9241600000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((695103053:ℚ)/1000000000),((70986743:ℚ)/100000000),((-177760229:ℚ)/255125000),((-6174133583:ℚ)/10300000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((2081278913:ℚ)/5000000000),((189683594526913995708816049498047563432674902347763781:ℚ)/825799818941244506835937500000000000000000000000000000),((44446146086927163792917:ℚ)/92416000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7010703023:ℚ)/10000000000),((1425698943:ℚ)/2000000000),((-3573096829:ℚ)/5150000000),((-62397733253:ℚ)/103475000000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((3963896517:ℚ)/10000000000),((49789183413751509410045294142253422076466284952077587516523:ℚ)/219373324246488281250000000000000000000000000000000000000000),((4441005776303868990815277:ℚ)/9241600000000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((3520268603:ℚ)/5000000000),((7158313907:ℚ)/10000000000),((-17954941721:ℚ)/25868750000),((-3484772737:ℚ)/5775000000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((772190879:ℚ)/2000000000),((14893956605968142411419146300456376953878940887102401908719:ℚ)/65606615827516365051269531250000000000000000000000000000000),((1110010151848642898133317:ℚ)/2310400000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((3535185019:ℚ)/5000000000),((7188131893:ℚ)/10000000000),((-18044395679:ℚ)/25987500000),((-31527035209:ℚ)/52212500000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((3755341437:ℚ)/10000000000),((705492968591342565514600822732348520498093687367596759394647:ℚ)/3106860565331730651855468750000000000000000000000000000000000),((1109766030347206634084293:ℚ)/2310400000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((7100201539:ℚ)/10000000000),((721794869:ℚ)/1000000000),((-1813384607:ℚ)/2610625000),((-63382216929:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3646825027:ℚ)/10000000000),((13896683015620162816250983051690064727509120311387515831907:ℚ)/61183522362584253692626953125000000000000000000000000000000),((4438076318993401475056373:ℚ)/9241600000000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-3:ℚ)/4),((-11:ℚ)/16),((3565015863:ℚ)/5000000000),((7247764313:ℚ)/10000000000),((-18223292939:ℚ)/26225000000),((-31855174493:ℚ)/52687500000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((1767568607:ℚ)/5000000000),((90997907353593788644237639709739316711876796413253068820159:ℚ)/400545319771094238281250000000000000000000000000000000000000),((1109269300260725280730397:ℚ)/2310400000000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((3579930309:ℚ)/5000000000),((7277578779:ℚ)/10000000000),((-18312736337:ℚ)/26343750000),((-32019233399:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((854991673:ℚ)/2500000000),((19394717228474396774214743732974889306536071441222518782594031:ℚ)/85349950173496341705322265625000000000000000000000000000000000),((1109016692069469477782853:ℚ)/2310400000000000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((898711029:ℚ)/1250000000),((913424013:ℚ)/1250000000),((-2300272039:ℚ)/3307812500),((-8045821319:ℚ)/13290625000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((3300948327:ℚ)/10000000000),((464987707432570319784250049402084074762631032301830395699439:ℚ)/2045801248044544661045074462890625000000000000000000000000000),((69297578461501873522533:ℚ)/144400000000000000000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((1443902917:ℚ)/2000000000),((3668602151:ℚ)/5000000000),((-9245806453:ℚ)/13290625000),((-12938932087:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((3177649149:ℚ)/10000000000),((475600274099960704097123704600044276954823782595683421308577:ℚ)/2092034050378819656372070312500000000000000000000000000000000),((177360478460583870805957:ℚ)/369664000000000000000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((3624669847:ℚ)/5000000000),((7367015389:ℚ)/10000000000),((-18581046167:ℚ)/26700000000),((-32511368317:ℚ)/53637500000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((1524774647:ℚ)/5000000000),((3891231151820256804796264093463445101170739866016877493001387:ℚ)/17112791573291162109375000000000000000000000000000000000000000),((1108241897249788647226717:ℚ)/2310400000000000000000000)⟩
theorem valid11 : Valid source24 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-3:ℚ)/4),((-11:ℚ)/16),((909895447:ℚ)/1250000000),((369841269:ℚ)/500000000),((-933523807:ℚ)/1340937500),((-8168849917:ℚ)/13468750000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1458007733:ℚ)/5000000000),((4263437975725805979485392873458542808115550437392203039:ℚ)/18745775302672979235649108886718750000000000000000000000),((69248623510816399009917:ℚ)/144400000000000000000000)⟩
theorem valid12 : Valid source24 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source24 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source24 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((913623281:ℚ)/1250000000),((745644213:ℚ)/1000000000),((-1884932639:ℚ)/2693750000),((-8209856091:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2776262957:ℚ)/10000000000),((16610293187040213504567947441254425362001551514793522530339:ℚ)/72174032755187225341796875000000000000000000000000000000000),((69258696333494047164093:ℚ)/144400000000000000000000)⟩
theorem valid13 : Valid source24 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source24 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((7368628023:ℚ)/10000000000),((7575663097:ℚ)/10000000000),((-19206989291:ℚ)/27175000000),((-66334908253:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2473839821:ℚ)/10000000000),((2679135594552468531184212311468751111796278675583144109963:ℚ)/11379498738356781005859375000000000000000000000000000000000),((4433811419631296296965277:ℚ)/9241600000000000000000000)⟩
theorem valid14 : Valid source24 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((3743948867:ℚ)/5000000000),((1562811567:ℚ)/2000000000),((-3984434701:ℚ)/5530000000),((-33823437537:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((171969203:ℚ)/1000000000),((29162557495988410268895484071451868289862777654511638411:ℚ)/118756146884375000000000000000000000000000000000000000000),((1105972894630795501978357:ℚ)/2310400000000000000000000)⟩
theorem valid15 : Valid source24 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((1545277009:ℚ)/2000000000),((4383554817:ℚ)/5000000000),((-11390664451:ℚ)/14300000000),((-14054047099:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((463745422642663562818027603662033720957414863487326451881:ℚ)/1537317478125000000000000000000000000000000000000000000000),((7640389:ℚ)/16000000)⟩
theorem valid16 : Valid source24 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((2169938079:ℚ)/2500000000),((1067146783:ℚ)/1000000000),((-2849440349:ℚ)/3240000000),((-20189318869:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((7136499058150317001783926862976632440416040323375243:ℚ)/19929037500000000000000000000000000000000000000000000),((7640389:ℚ)/16000000)⟩
theorem valid17 : Valid source24 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((119:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((10584560359:ℚ)/10000000000),((6287215497:ℚ)/5000000000),((-17101646491:ℚ)/20000000000),((-101710163949:ℚ)/190400000000),((4638999999:ℚ)/5000000000),((4772478993:ℚ)/5000000000),((1911621469:ℚ)/5000000000),(0:ℚ),((89256003461539613426664757371866440027535546477556516790837:ℚ)/265518750000000000000000000000000000000000000000000000000000),((7640389:ℚ)/16000000)⟩
theorem valid18 : Valid source24 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((119:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((119:ℚ)/100),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((3121957249:ℚ)/2500000000),((14476576807:ℚ)/10000000000),((-39909730421:ℚ)/47600000000),((-10220509913:ℚ)/18400000000),((9544957981:ℚ)/10000000000),(1:ℚ),((189269891:ℚ)/625000000),(0:ℚ),((8199516383544203713914533337916713494505242594469734366183:ℚ)/25469974600000000000000000000000000000000000000000000000000),((7640389:ℚ)/16000000)⟩
theorem valid19 : Valid source24 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source24 nn0 nn1 Qcell ((119:ℚ)/100) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet19 valid19
private theorem node0_2 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source24 nn0 nn1 Qcell ((2041:ℚ)/3200) ((2079:ℚ)/3200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source24 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source24 nn0 nn1 Qcell ((843:ℚ)/1280) ((4253:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source24 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4253:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source24 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((4253:ℚ)/6400) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source24 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source24 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source24 nn0 nn1 Qcell ((4291:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source24 nn0 nn1 Qcell ((4253:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound source24 nn0 nn1 Qcell ((4253:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC05
#check @N11Formalization.C450Source24GroupedC05.bound
#print axioms N11Formalization.C450Source24GroupedC05.valid0
#print axioms N11Formalization.C450Source24GroupedC05.valid1
#print axioms N11Formalization.C450Source24GroupedC05.valid2
#print axioms N11Formalization.C450Source24GroupedC05.valid3
#print axioms N11Formalization.C450Source24GroupedC05.valid4
#print axioms N11Formalization.C450Source24GroupedC05.valid5
#print axioms N11Formalization.C450Source24GroupedC05.valid6
#print axioms N11Formalization.C450Source24GroupedC05.valid7
#print axioms N11Formalization.C450Source24GroupedC05.valid8
#print axioms N11Formalization.C450Source24GroupedC05.valid9
#print axioms N11Formalization.C450Source24GroupedC05.valid10
#print axioms N11Formalization.C450Source24GroupedC05.valid11
#print axioms N11Formalization.C450Source24GroupedC05.valid12
#print axioms N11Formalization.C450Source24GroupedC05.valid13
#print axioms N11Formalization.C450Source24GroupedC05.valid14
#print axioms N11Formalization.C450Source24GroupedC05.valid15
#print axioms N11Formalization.C450Source24GroupedC05.valid16
#print axioms N11Formalization.C450Source24GroupedC05.valid17
#print axioms N11Formalization.C450Source24GroupedC05.valid18
#print axioms N11Formalization.C450Source24GroupedC05.valid19
#print axioms N11Formalization.C450Source24GroupedC05.bound
#print axioms N11Formalization.C450Source24GroupedC05.endpoint_checks
