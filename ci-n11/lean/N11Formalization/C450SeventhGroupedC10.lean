import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((1960071:ℚ)/3125000),((653888151:ℚ)/1000000000),((-4257217057:ℚ)/9920000000),((-5280213:ℚ)/16093750),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6000753753:ℚ)/10000000000),((2306455112203304828775215022948808075208266661:ℚ)/201907974481582641601562500000000000000000000000),((3736962050092023700949653:ℚ)/55449600000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((6509829541:ℚ)/10000000000),((3388255163:ℚ)/5000000000),((-22117786141:ℚ)/51500000000),((-5869829541:ℚ)/17800000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5422367977:ℚ)/10000000000),((5165441741331359376576796260254028717403653981008632563:ℚ)/453823793750000000000000000000000000000000000000000000000),((31008256744883556054856319:ℚ)/462080000000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((3373712297:ℚ)/5000000000),((3447660677:ℚ)/5000000000),((-22533624739:ℚ)/53400000000),((-9161136891:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((597765381:ℚ)/1250000000),((185762318536560778577808755845343651941744984364844815057:ℚ)/16744413540087890625000000000000000000000000000000000000000),((30842673541930760916038079:ℚ)/462080000000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((6866219627:ℚ)/10000000000),((278189043:ℚ)/400000000),((-1819323301:ℚ)/4348000000),((-6226219627:ℚ)/18275000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((8653247:ℚ)/19531250),((56800928968963889401199945302747722499699603278516657101:ℚ)/5183125580041503906250000000000000000000000000000000000000),((590594058981319839206797:ℚ)/8871936000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((3462808279:ℚ)/5000000000),((1753532571:ℚ)/2500000000),((-11474727997:ℚ)/27412500000),((-9428424837:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1061125213:ℚ)/2500000000),((24798210165971302228692978865901391406191164452578414901:ℚ)/2263570817633056640625000000000000000000000000000000000000),((23045741471619531648993373:ℚ)/346560000000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((6985013113:ℚ)/10000000000),((1768383499:ℚ)/2500000000),((-11578684493:ℚ)/27650000000),((-19035039339:ℚ)/55775000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((2025275661:ℚ)/5000000000),((205241645276483945716572376051405319775337012699689082363:ℚ)/18740186438668823242187500000000000000000000000000000000000),((7673838117335972260900751:ℚ)/115520000000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((7044409299:ℚ)/10000000000),((3566468611:ℚ)/5000000000),((-23365280277:ℚ)/55775000000),((-6404409299:ℚ)/18750000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3847402303:ℚ)/10000000000),((5896500980927380050187988255280336488226981464356427167:ℚ)/538560748100280761718750000000000000000000000000000000000),((30663198753848890075117071:ℚ)/462080000000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-7:ℚ)/16),((-3:ℚ)/8),((887975641:ℚ)/1250000000),((7162638657:ℚ)/10000000000),((-46938470599:ℚ)/112500000000),((-2423926923:ℚ)/7060937500),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((1816753583:ℚ)/5000000000),((107780414272143692770710831118573584094358920970389607:ℚ)/9901013055217266082763671875000000000000000000000000000),((367466352269254710346400197:ℚ)/5544960000000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((7133502911:ℚ)/10000000000),((287693599:ℚ)/400000000),((-1885855193:ℚ)/4519000000),((-19480508733:ℚ)/56725000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((17609603:ℚ)/50000000),((70140351987762762580090405949149072585621878375640220827:ℚ)/6444005246773803710937500000000000000000000000000000000000),((195879759524911854270551:ℚ)/2957312000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-7:ℚ)/16),((-3:ℚ)/8),((223850019:ℚ)/312500000),((3611020589:ℚ)/5000000000),((-23677144123:ℚ)/56725000000),((-203850019:ℚ)/593359375),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((425854791:ℚ)/1250000000),((64485536984517685663043462157004163561708911616395511:ℚ)/5925130697765201330184936523437500000000000000000000000),((30590266101678545091154671:ℚ)/462080000000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((7192898219:ℚ)/10000000000),((7251742267:ℚ)/10000000000),((-47562195869:ℚ)/113925000000),((-19658694657:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((3287892779:ℚ)/10000000000),((29002427056955413210513136168190241378367760744079914560101:ℚ)/2665122259800000000000000000000000000000000000000000000000000),((122297428200178693459279039:ℚ)/1848320000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((-7:ℚ)/16),((-3:ℚ)/8),((7222595747:ℚ)/10000000000),((1820360811:ℚ)/2500000000),((-11942525677:ℚ)/28600000000),((-19747787241:ℚ)/57437500000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((3164647817:ℚ)/10000000000),((921389294167769467807391179908508466516076207832931776007:ℚ)/84678400373077392578125000000000000000000000000000000000000),((22918863951396152250326413:ℚ)/346560000000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((906536649:ℚ)/1250000000),((7311144109:ℚ)/10000000000),((-47978008763:ℚ)/114875000000),((-826536649:ℚ)/2403125000),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1518289713:ℚ)/5000000000),((50815970239693063771532981646559720993092798514327:ℚ)/4670634757775813341140747070312500000000000000000000),((122170603026831639009691631:ℚ)/1848320000000000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((1456398111:ℚ)/2000000000),((7370545513:ℚ)/10000000000),((-48393818591:ℚ)/115350000000),((-3985194333:ℚ)/11630000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2903048729:ℚ)/10000000000),((124021221169352669496511506466068264498076758764008622711:ℚ)/11340619007278125000000000000000000000000000000000000000000),((122144299328854939937782919:ℚ)/1848320000000000000000000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-7:ℚ)/16),((-3:ℚ)/8),((3670692519:ℚ)/5000000000),((928743311:ℚ)/1250000000),((-6101203177:ℚ)/14537500000),((-10052077557:ℚ)/29312500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((261622027:ℚ)/1000000000),((1000758072627227060357880061194616647901628403734888048711:ℚ)/91535238317108154296875000000000000000000000000000000000000),((1906541659528634582565471:ℚ)/28880000000000000000000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((3700389603:ℚ)/5000000000),((1497869409:ℚ)/2000000000),((-9845085863:ℚ)/23450000000),((-3380389603:ℚ)/9850000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2294715333:ℚ)/10000000000),((3827335107967596062111921431272979687019793789587606103:ℚ)/350164056347656250000000000000000000000000000000000000000),((14627235522427893280441093:ℚ)/221798400000000000000000000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((3730086533:ℚ)/5000000000),((3804073473:ℚ)/5000000000),((-25028514311:ℚ)/59100000000),((-10230259599:ℚ)/30025000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1921196263:ℚ)/10000000000),((137929729415580896829544774529959903990354742935536855449:ℚ)/12497598244519042968750000000000000000000000000000000000000),((32061771564989381:ℚ)/486400000000000000)⟩
theorem valid16 : Valid seventh packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-7:ℚ)/16),((-3:ℚ)/8),((757895989:ℚ)/1000000000),((1931736323:ℚ)/2500000000),((-12722154261:ℚ)/30025000000),((-2081687967:ℚ)/6100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((372136659:ℚ)/5000000000),((9394920272728919773323398682624379419778767122908430383:ℚ)/851888065625000000000000000000000000000000000000000000000),((6391317843552373:ℚ)/97280000000000000)⟩
theorem valid17 : Valid seventh packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((3848872783:ℚ)/5000000000),((2050531123:ℚ)/2500000000),((-13553717861:ℚ)/30500000000),((-3528872783:ℚ)/10800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((930107286725731375140018299755545442046086002151860689:ℚ)/80044200000000000000000000000000000000000000000000000000),((4202363:ℚ)/64000000)⟩
theorem valid18 : Valid seventh packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((4086438903:ℚ)/5000000000),((10102670981:ℚ)/10000000000),((-22506232289:ℚ)/43200000000),((-11299316709:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((72751894444171144913451212969415921192874632718210739063:ℚ)/5400000000000000000000000000000000000000000000000000000000),((4202363:ℚ)/64000000)⟩
theorem valid19 : Valid seventh packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((100732811:ℚ)/100000000),((13903312399:ℚ)/10000000000),((-94123186793:ℚ)/160000000000),((-94332811:ℚ)/368000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1801186973899088461024463811553831994440840734313:ℚ)/116803200000000000000000000000000000000000000000000),((4202363:ℚ)/64000000)⟩
theorem valid20 : Valid seventh packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound seventh nn0 nn1 Qcell ((4519:ℚ)/6400) ((4557:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((4557:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((4557:ℚ)/6400) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((4557:ℚ)/6400) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound seventh nn0 nn1 Qcell ((4557:ℚ)/6400) ((919:ℚ)/1280) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound seventh nn0 nn1 Qcell ((919:ℚ)/1280) ((469:ℚ)/640) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound seventh nn0 nn1 Qcell ((4557:ℚ)/6400) ((469:ℚ)/640) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound seventh nn0 nn1 Qcell ((4557:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC10
#check @N11Formalization.C450SeventhGroupedC10.bound
#print axioms N11Formalization.C450SeventhGroupedC10.valid0
#print axioms N11Formalization.C450SeventhGroupedC10.valid1
#print axioms N11Formalization.C450SeventhGroupedC10.valid2
#print axioms N11Formalization.C450SeventhGroupedC10.valid3
#print axioms N11Formalization.C450SeventhGroupedC10.valid4
#print axioms N11Formalization.C450SeventhGroupedC10.valid5
#print axioms N11Formalization.C450SeventhGroupedC10.valid6
#print axioms N11Formalization.C450SeventhGroupedC10.valid7
#print axioms N11Formalization.C450SeventhGroupedC10.valid8
#print axioms N11Formalization.C450SeventhGroupedC10.valid9
#print axioms N11Formalization.C450SeventhGroupedC10.valid10
#print axioms N11Formalization.C450SeventhGroupedC10.valid11
#print axioms N11Formalization.C450SeventhGroupedC10.valid12
#print axioms N11Formalization.C450SeventhGroupedC10.valid13
#print axioms N11Formalization.C450SeventhGroupedC10.valid14
#print axioms N11Formalization.C450SeventhGroupedC10.valid15
#print axioms N11Formalization.C450SeventhGroupedC10.valid16
#print axioms N11Formalization.C450SeventhGroupedC10.valid17
#print axioms N11Formalization.C450SeventhGroupedC10.valid18
#print axioms N11Formalization.C450SeventhGroupedC10.valid19
#print axioms N11Formalization.C450SeventhGroupedC10.valid20
#print axioms N11Formalization.C450SeventhGroupedC10.bound
#print axioms N11Formalization.C450SeventhGroupedC10.endpoint_checks
