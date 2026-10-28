import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((3195157507:ℚ)/5000000000),((6674712657:ℚ)/10000000000),((-53672413913:ℚ)/99200000000),((-2755157507:ℚ)/6437500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1429949683:ℚ)/2500000000),((118287959773777226326027370691311478475547799263321659:ℚ)/3230527591705322265625000000000000000000000000000000000),((1377520932610027541234929:ℚ)/8664000000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((1657043213:ℚ)/2500000000),((1698412319:ℚ)/2500000000),((-13685710871:ℚ)/25750000000),((-1437043213:ℚ)/3278125000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((639076801:ℚ)/1250000000),((12567532780053938738789852766007709041290422611218677:ℚ)/354334792038798332214355468750000000000000000000000000),((57086991970018883584079:ℚ)/361000000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((6747092029:ℚ)/10000000000),((6912579241:ℚ)/10000000000),((-55813213169:ℚ)/104900000000),((-1955697343:ℚ)/4450000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((956614767:ℚ)/2000000000),((320089558591075964265413037705047511075652347099140009:ℚ)/9027251965332031250000000000000000000000000000000000000),((455518267873213317139217:ℚ)/2888000000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((6866005173:ℚ)/10000000000),((6972041837:ℚ)/10000000000),((-56348376533:ℚ)/106800000000),((-5986005173:ℚ)/13468750000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2215560321:ℚ)/5000000000),((34771667406178780782768866893681984276816280395954007:ℚ)/995435686642304062843322753906250000000000000000000000),((454281403519754905177833:ℚ)/2888000000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((6925459583:ℚ)/10000000000),((70315029:ℚ)/100000000),((-568835261:ℚ)/1077500000),((-6045459583:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4245002369:ℚ)/10000000000),((14753157944705193094944456539393835740099217469233304711:ℚ)/422333932337188720703125000000000000000000000000000000000),((57308706248194697027:ℚ)/364800000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((6984912603:ℚ)/10000000000),((1772740617:ℚ)/2500000000),((-14354665553:ℚ)/27175000000),((-6104912603:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4050886909:ℚ)/10000000000),((353642190224283831456457797004371012083541924981824561:ℚ)/10123292148518562316894531250000000000000000000000000000),((679660469897105665891277:ℚ)/4332000000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-9:ℚ)/16),((-1:ℚ)/2),((1761091067:ℚ)/2500000000),((890086463:ℚ)/1250000000),((-7210778167:ℚ)/13706250000),((-1541091067:ℚ)/3441406250),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((3847560169:ℚ)/10000000000),((151369393443950424307300627112600658460722947815867219:ℚ)/4364319219349999912083148956298828125000000000000000000),((56561164426891284301839:ℚ)/361000000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((7074089603:ℚ)/10000000000),((357521029:ℚ)/500000000),((-2897689261:ℚ)/5506250000),((-6194089603:ℚ)/13825000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((748394959:ℚ)/2000000000),((492829440880671828841863968329301247479420162139566389:ℚ)/14208603299808502197265625000000000000000000000000000000),((9043923611343478254671:ℚ)/57760000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((7103814613:ℚ)/10000000000),((3590074551:ℚ)/5000000000),((-29110670959:ℚ)/55300000000),((-2074604871:ℚ)/4628125000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3633472051:ℚ)/10000000000),((185698473589632441672546713297024950887981869511885889:ℚ)/5353532151797413825988769531250000000000000000000000000),((677854768658263919704517:ℚ)/4332000000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((3566769651:ℚ)/5000000000),((3604938637:ℚ)/5000000000),((-29244447733:ℚ)/55537500000),((-3126769651:ℚ)/6971875000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((880445447:ℚ)/2500000000),((1275130730862873228213603059335395726904066352439362831:ℚ)/36759122977564483880996704101562500000000000000000000000),((56451288873260289984179:ℚ)/361000000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((7163263673:ℚ)/10000000000),((72396051:ℚ)/100000000),((-587564459:ℚ)/1115500000),((-6283263673:ℚ)/14003125000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((3406589973:ℚ)/10000000000),((3320509474433700161828685192056699643614398190176330009:ℚ)/95718193400416851043701171875000000000000000000000000000),((1083162182821972774943:ℚ)/6931200000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-9:ℚ)/16),((-1:ℚ)/2),((7192987731:ℚ)/10000000000),((1453866517:ℚ)/2000000000),((-11804798653:ℚ)/22405000000),((-6312987731:ℚ)/14062500000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((3287528003:ℚ)/10000000000),((219882810259443133192732173960210137661276895385531471:ℚ)/6338133243843913078308105468750000000000000000000000000),((18040998984838905400373:ℚ)/115520000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((180567787:ℚ)/250000000),((7299059733:ℚ)/10000000000),((-59291537597:ℚ)/112500000000),((-158567787:ℚ)/353046875),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((1582079231:ℚ)/5000000000),((21468825622762767501691875338493298629110142753101:ℚ)/618813315951079130172729492187500000000000000000000),((1352197518833111205164869:ℚ)/8664000000000000000000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7252434923:ℚ)/10000000000),((1832196637:ℚ)/2500000000),((-14889769733:ℚ)/28243750000),((-6372434923:ℚ)/14181250000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((758988921:ℚ)/2500000000),((436668981726166266676900639873375675030046435907786491:ℚ)/12585947747605085372924804687500000000000000000000000000),((225220085556583887258239:ℚ)/1444000000000000000000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((1456431613:ℚ)/2000000000),((7388239197:ℚ)/10000000000),((-60094152773:ℚ)/113450000000),((-1280431613:ℚ)/2860000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((290227863:ℚ)/1000000000),((724359596209860495637898588726645610469735503034739359:ℚ)/20734455259375000000000000000000000000000000000000000000),((1350540785741964008981539:ℚ)/8664000000000000000000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7341603459:ℚ)/10000000000),((1489538113:ℚ)/2000000000),((-12125843017:ℚ)/22880000000),((-6461603459:ℚ)/14418750000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((261510889:ℚ)/1000000000),((19042082835910379257053322213123340967243321483767:ℚ)/545076798445545136928558349609375000000000000000000),((17983860669941648358733:ℚ)/115520000000000000000000)⟩
theorem valid15 : Valid source12 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((7401047691:ℚ)/10000000000),((7507140683:ℚ)/10000000000),((-61164266147:ℚ)/115350000000),((-6521047691:ℚ)/14537500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2293161729:ℚ)/10000000000),((96722174511672141206602243162910617421420467487645300119:ℚ)/2768705812323760986328125000000000000000000000000000000000),((449013303625827291846773:ℚ)/2888000000000000000000000)⟩
theorem valid16 : Valid source12 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((7460490791:ℚ)/10000000000),((762603729:ℚ)/1000000000),((-6223433561:ℚ)/11630000000),((-6580490791:ℚ)/14775000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1919005549:ℚ)/10000000000),((480152176522277507388722577829206563651746295609223697:ℚ)/13567457273864746093750000000000000000000000000000000000),((151062888673019653:ℚ)/972800000000000000)⟩
theorem valid17 : Valid source12 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-9:ℚ)/16),((-1:ℚ)/2),((7579373701:ℚ)/10000000000),((393190839:ℚ)/500000000),((-3218717551:ℚ)/5910000000),((-6699373701:ℚ)/15250000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((368457273:ℚ)/5000000000),((486627573960986403033845895225543905883435327641344873:ℚ)/13422308349609375000000000000000000000000000000000000000),((150625884963141183:ℚ)/972800000000000000)⟩
theorem valid18 : Valid source12 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((7817127081:ℚ)/10000000000),((8339326511:ℚ)/10000000000),((-68653938599:ℚ)/122000000000),((-6937127081:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((141900595449850416023536827339329375888335751734778089:ℚ)/3752071875000000000000000000000000000000000000000000000),((19809219:ℚ)/128000000)⟩
theorem valid19 : Valid source12 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((20731473:ℚ)/25000000),((640055039:ℚ)/625000000),((-5360495351:ℚ)/8100000000),((-18531473:ℚ)/50000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3197866020858319788656933615988715154642488273196131:ℚ)/69198046875000000000000000000000000000000000000000000),((19809219:ℚ)/128000000)⟩
theorem valid20 : Valid source12 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((2548499549:ℚ)/2500000000),((7021352053:ℚ)/5000000000),((-59992168477:ℚ)/80000000000),((-2328499549:ℚ)/6900000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((4374461472790616724580774063191518559932418160627785597193:ℚ)/79350000000000000000000000000000000000000000000000000000000),((19809219:ℚ)/128000000)⟩
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
    CellBound source12 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source12 nn0 nn1 Qcell ((4443:ℚ)/6400) ((4481:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((4481:ℚ)/6400) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4481:ℚ)/6400) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((4481:ℚ)/6400) :=
  cell_join node0_5 node5_11
private theorem node11_13 :
    CellBound source12 nn0 nn1 Qcell ((4481:ℚ)/6400) ((4519:ℚ)/6400) :=
  cell_join leaf11 leaf12
private theorem node14_16 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source12 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join leaf13 node14_16
private theorem node11_16 :
    CellBound source12 nn0 nn1 Qcell ((4481:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join node11_13 node13_16
private theorem node17_19 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf16 node17_19
private theorem node20_22 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf19 node20_22
private theorem node16_22 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node16_19 node19_22
private theorem node11_22 :
    CellBound source12 nn0 nn1 Qcell ((4481:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node11_16 node16_22
private theorem node0_22 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_22
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_22
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21]
theorem packet_count : packets.length = 22 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC08
#check @N11Formalization.C450Source12GroupedC08.bound
#print axioms N11Formalization.C450Source12GroupedC08.valid0
#print axioms N11Formalization.C450Source12GroupedC08.valid1
#print axioms N11Formalization.C450Source12GroupedC08.valid2
#print axioms N11Formalization.C450Source12GroupedC08.valid3
#print axioms N11Formalization.C450Source12GroupedC08.valid4
#print axioms N11Formalization.C450Source12GroupedC08.valid5
#print axioms N11Formalization.C450Source12GroupedC08.valid6
#print axioms N11Formalization.C450Source12GroupedC08.valid7
#print axioms N11Formalization.C450Source12GroupedC08.valid8
#print axioms N11Formalization.C450Source12GroupedC08.valid9
#print axioms N11Formalization.C450Source12GroupedC08.valid10
#print axioms N11Formalization.C450Source12GroupedC08.valid11
#print axioms N11Formalization.C450Source12GroupedC08.valid12
#print axioms N11Formalization.C450Source12GroupedC08.valid13
#print axioms N11Formalization.C450Source12GroupedC08.valid14
#print axioms N11Formalization.C450Source12GroupedC08.valid15
#print axioms N11Formalization.C450Source12GroupedC08.valid16
#print axioms N11Formalization.C450Source12GroupedC08.valid17
#print axioms N11Formalization.C450Source12GroupedC08.valid18
#print axioms N11Formalization.C450Source12GroupedC08.valid19
#print axioms N11Formalization.C450Source12GroupedC08.valid20
#print axioms N11Formalization.C450Source12GroupedC08.valid21
#print axioms N11Formalization.C450Source12GroupedC08.bound
#print axioms N11Formalization.C450Source12GroupedC08.endpoint_checks
