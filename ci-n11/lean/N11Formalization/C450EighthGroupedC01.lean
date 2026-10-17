import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((200763671:ℚ)/312500000),((6717500003:ℚ)/10000000000),(-1:ℚ),((-574291013:ℚ)/643750000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5636311369:ℚ)/10000000000),((37984079988934109448007362857201:ℚ)/2072070312500000000000000000000000),((35486549280703142360697:ℚ)/152000000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((6661958227:ℚ)/10000000000),((3418125001:ℚ)/5000000000),(-1:ℚ),((-19089874681:ℚ)/20980000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5021007961:ℚ)/10000000000),((19227437568620795140286998197878973:ℚ)/1100401000000000000000000000000000000),((691640426580963922283590467:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((6780718041:ℚ)/10000000000),((3477500001:ℚ)/5000000000),(-1:ℚ),((-19446154123:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4686037927:ℚ)/10000000000),((19888690748488017002300836044141031:ℚ)/1140624000000000000000000000000000000),((692957774326526819260574363:ℚ)/2957312000000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),(-1:ℚ),((-15:ℚ)/16),((1379895501:ℚ)/2000000000),((3507187501:ℚ)/5000000000),(-1:ℚ),((-3960486503:ℚ)/4310000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4327259919:ℚ)/10000000000),((296645687574621314494577004280303:ℚ)/17415093750000000000000000000000000),((1460126362498485070177617:ℚ)/6225920000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((869857139:ℚ)/1250000000),((3536875001:ℚ)/5000000000),(-1:ℚ),((-2497571417:ℚ)/2717500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((827402987:ℚ)/2000000000),((628524518841224947128283805194579:ℚ)/36924031250000000000000000000000000),((10847140799176536251678083:ℚ)/46208000000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7018236639:ℚ)/10000000000),((7103437503:ℚ)/10000000000),(-1:ℚ),((-20158709917:ℚ)/21835000000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((157525713:ℚ)/400000000),((30083917760278010627330302642661497:ℚ)/1787877093750000000000000000000000000),((694516931579596613811651083:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((1761981593:ℚ)/2500000000),((3566562501:ℚ)/5000000000),(-1:ℚ),((-5061944779:ℚ)/5482500000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((383505333:ℚ)/1000000000),((316024434607279273015409720335979:ℚ)/18786128906250000000000000000000000),((43427812801264466303379227:ℚ)/184832000000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),(-1:ℚ),((-15:ℚ)/16),((7077616087:ℚ)/10000000000),((3581406251:ℚ)/5000000000),(-1:ℚ),((-20336848261:ℚ)/22025000000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((3729259857:ℚ)/10000000000),((20395942393924738876106324217539873:ℚ)/1212751562500000000000000000000000000),((695172957720620787043243387:ℚ)/2957312000000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((881:ℚ)/1280),((8829:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((3553652891:ℚ)/5000000000),((7177656253:ℚ)/10000000000),(-1:ℚ),((-10212958673:ℚ)/11036250000),((301591713:ℚ)/312500000),((9656888659:ℚ)/10000000000),((2649962557:ℚ)/10000000000),((724104981:ℚ)/2000000000),((6789154611741597290185290774059069:ℚ)/405996046875000000000000000000000000),((173830624178731145977858963:ℚ)/739328000000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((881:ℚ)/1280) ((8829:ℚ)/12800) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8829:ℚ)/12800),((553:ℚ)/800),(-1:ℚ),((-15:ℚ)/16),((3561075311:ℚ)/5000000000),((7192500003:ℚ)/10000000000),(-1:ℚ),((-10235225933:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((9650934821:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3564970397:ℚ)/10000000000),((182616094696597525086132561776039:ℚ)/10921750000000000000000000000000000),((173871591964715122335130283:ℚ)/739328000000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((8829:ℚ)/12800) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((8867:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((3568497729:ℚ)/5000000000),((900917969:ℚ)/1250000000),(-1:ℚ),((-10257493187:ℚ)/11083750000),((2409799777:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((673601917:ℚ)/2500000000),((701714901:ℚ)/2000000000),((20538730764676275614751906266474351:ℚ)/1228495140625000000000000000000000000),((173912552225594363124400843:ℚ)/739328000000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((8867:ℚ)/12800) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8867:ℚ)/12800),((4443:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7151840289:ℚ)/10000000000),((3611093751:ℚ)/5000000000),(-1:ℚ),((-20559520867:ℚ)/22215000000),((4816708251:ℚ)/5000000000),((9639199113:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3451295927:ℚ)/10000000000),((2291627584473418974489110476934949:ℚ)/137085062500000000000000000000000000),((695814019870499123562396683:ℚ)/2957312000000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((8867:ℚ)/12800) ((4443:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4443:ℚ)/6400),((1781:ℚ)/2560),(-1:ℚ),((-15:ℚ)/16),((1791671279:ℚ)/2500000000),((1809257813:ℚ)/2500000000),(-1:ℚ),((-5151013837:ℚ)/5565625000),((9627690243:ℚ)/10000000000),((9633416507:ℚ)/10000000000),((2737309683:ℚ)/10000000000),((848272473:ℚ)/2500000000),((1593135002222786813779317529601443:ℚ)/95311328125000000000000000000000000),((43498612546891619604464043:ℚ)/184832000000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((4443:ℚ)/6400) ((1781:ℚ)/2560) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1781:ℚ)/2560),((2231:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((3590764969:ℚ)/5000000000),((3625937501:ℚ)/5000000000),(-1:ℚ),((-10324294907:ℚ)/11155000000),((2405504993:ℚ)/2500000000),((1203461281:ℚ)/1250000000),((551641531:ℚ)/2000000000),((666781553:ℚ)/2000000000),((2599631377553942489929508568699283:ℚ)/155542531250000000000000000000000000),((174035387885670703727495803:ℚ)/739328000000000000000000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((1781:ℚ)/2560) ((2231:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2231:ℚ)/3200),((8943:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((1439274951:ℚ)/2000000000),((7266718753:ℚ)/10000000000),(-1:ℚ),((-376238623:ℚ)/406500000),((961640533:ℚ)/1000000000),((9622019977:ℚ)/10000000000),((555749933:ℚ)/2000000000),((1636848271:ℚ)/5000000000),((690364832471898236403245861809:ℚ)/41310562500000000000000000000000),((27852210890391663609416923:ℚ)/118292480000000000000000000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((8943:ℚ)/12800) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((8943:ℚ)/12800),((4481:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((450701223:ℚ)/625000000),((7281562503:ℚ)/10000000000),(-1:ℚ),((-1296103669:ℚ)/1400312500),((1922169193:ℚ)/2000000000),((1923281067:ℚ)/2000000000),((349868089:ℚ)/1250000000),((200774893:ℚ)/625000000),((3145531567040008939083878396810977:ℚ)/188244009375000000000000000000000000),((143188520328251482984793:ℚ)/608000000000000000000000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell ((8943:ℚ)/12800) ((4481:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((4481:ℚ)/6400),((8981:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7226064377:ℚ)/10000000000),((1824101563:ℚ)/2500000000),(-1:ℚ),((-2968884733:ℚ)/3207500000),((4802670763:ℚ)/5000000000),((961084597:ℚ)/1000000000),((563760281:ℚ)/2000000000),((125997979:ℚ)/400000000),((429736199214438166074843080868733:ℚ)/25720140625000000000000000000000000),((696632623393178009340946267:ℚ)/2957312000000000000000000000)⟩
theorem valid16 : Valid eighth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound eighth nn0 nn1 Qcell ((4481:ℚ)/6400) ((8981:ℚ)/12800) :=
  cell_of_packet eighth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((8981:ℚ)/12800),((45:ℚ)/64),(-1:ℚ),((-15:ℚ)/16),((7240909181:ℚ)/10000000000),((3655625001:ℚ)/5000000000),(-1:ℚ),((-20826727543:ℚ)/22500000000),((599993229:ℚ)/625000000),((9605341531:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((617256039:ℚ)/2000000000),((881005253309766037057392343643933:ℚ)/52734375000000000000000000000000000),((696796253834515791393111203:ℚ)/2957312000000000000000000000)⟩
theorem valid17 : Valid eighth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound eighth nn0 nn1 Qcell ((8981:ℚ)/12800) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((362787699:ℚ)/500000000),((3670468751:ℚ)/5000000000),(-1:ℚ),((-1043563097:ℚ)/1129750000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((3021313223:ℚ)/10000000000),((214341465892610362720849303657949:ℚ)/12763350625000000000000000000000000),((1742845369391619024987523:ℚ)/7393280000000000000000000)⟩
theorem valid18 : Valid eighth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((3642721783:ℚ)/5000000000),((7370625003:ℚ)/10000000000),(-1:ℚ),((-10480165349:ℚ)/11345000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((2887133753:ℚ)/10000000000),((540245795636512823191705362550583:ℚ)/32177256250000000000000000000000000),((174366314553110442654300347:ℚ)/739328000000000000000000000)⟩
theorem valid19 : Valid eighth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound eighth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((3657566567:ℚ)/5000000000),((3700156251:ℚ)/5000000000),(-1:ℚ),((-10524699701:ℚ)/11392500000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((2746598171:ℚ)/10000000000),((10893136689830162230231187843472697:ℚ)/648945281250000000000000000000000000),((174448062073433024808907547:ℚ)/739328000000000000000000000)⟩
theorem valid20 : Valid eighth packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((1468964537:ℚ)/2000000000),((7430000003:ℚ)/10000000000),(-1:ℚ),((-4227693611:ℚ)/4576000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((2598674821:ℚ)/10000000000),((135159820424070118187420302857363:ℚ)/8053760000000000000000000000000000),((1469724459047957860955673:ℚ)/6225920000000000000000000)⟩
theorem valid21 : Valid eighth packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound eighth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7374512219:ℚ)/10000000000),((3744687501:ℚ)/5000000000),(-1:ℚ),((-21227536657:ℚ)/23070000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1221010433:ℚ)/5000000000),((93970655360154894122510549180371:ℚ)/5544009375000000000000000000000000),((698802454562746765706454803:ℚ)/2957312000000000000000000000)⟩
theorem valid22 : Valid eighth packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((1858472809:ℚ)/2500000000),((7548750003:ℚ)/10000000000),(-1:ℚ),((-5351418427:ℚ)/5815000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1047294153:ℚ)/5000000000),((2864212486932192272731278156678463:ℚ)/169071125000000000000000000000000000),((43715974519022892966208763:ℚ)/184832000000000000000000000)⟩
theorem valid23 : Valid eighth packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),(-1:ℚ),((-15:ℚ)/16),((1873317547:ℚ)/2500000000),((3833750001:ℚ)/5000000000),(-1:ℚ),((-5395952641:ℚ)/5910000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1677878989:ℚ)/10000000000),((1507150845197372180723418050921869:ℚ)/87320250000000000000000000000000000),((43750666020269893616861107:ℚ)/184832000000000000000000000)⟩
theorem valid24 : Valid eighth packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),(-1:ℚ),((-15:ℚ)/16),((7612027901:ℚ)/10000000000),((3952500001:ℚ)/5000000000),(-1:ℚ),((-21940083703:ℚ)/24400000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((159425550600461341545716646411699913:ℚ)/8930400000000000000000000000000000000),((242347877:ℚ)/1024000000)⟩
theorem valid25 : Valid eighth packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((7849542607:ℚ)/10000000000),((8380000003:ℚ)/10000000000),(-1:ℚ),((-22652627821:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((63420438605749052698972140994044341:ℚ)/3359232000000000000000000000000000000),((242347877:ℚ)/1024000000)⟩
theorem valid26 : Valid eighth packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((8324569431:ℚ)/10000000000),((5140000001:ℚ)/5000000000),(-1:ℚ),((-24077708293:ℚ)/32000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((357870512561121464047528884434541973:ℚ)/15360000000000000000000000000000000000),((242347877:ℚ)/1024000000)⟩
theorem valid27 : Valid eighth packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((10224651241:ℚ)/10000000000),((14080000003:ℚ)/10000000000),(-1:ℚ),((-29777953723:ℚ)/44160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((25882220604895272820760051:ℚ)/975052800000000000000000000),((242347877:ℚ)/1024000000)⟩
theorem valid28 : Valid eighth packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet28 valid28
private theorem node1_3 :
    CellBound eighth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound eighth nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound eighth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound eighth nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound eighth nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_7 node7_14
private theorem node15_17 :
    CellBound eighth nn0 nn1 Qcell ((8943:ℚ)/12800) ((8981:ℚ)/12800) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((8981:ℚ)/12800) :=
  cell_join leaf14 node15_17
private theorem node17_19 :
    CellBound eighth nn0 nn1 Qcell ((8981:ℚ)/12800) ((4519:ℚ)/6400) :=
  cell_join leaf17 leaf18
private theorem node19_21 :
    CellBound eighth nn0 nn1 Qcell ((4519:ℚ)/6400) ((4557:ℚ)/6400) :=
  cell_join leaf19 leaf20
private theorem node17_21 :
    CellBound eighth nn0 nn1 Qcell ((8981:ℚ)/12800) ((4557:ℚ)/6400) :=
  cell_join node17_19 node19_21
private theorem node14_21 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_join node14_17 node17_21
private theorem node21_23 :
    CellBound eighth nn0 nn1 Qcell ((4557:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join leaf21 leaf22
private theorem node23_25 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf23 leaf24
private theorem node21_25 :
    CellBound eighth nn0 nn1 Qcell ((4557:ℚ)/6400) ((591:ℚ)/800) :=
  cell_join node21_23 node23_25
private theorem node25_27 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf25 leaf26
private theorem node27_29 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf27 leaf28
private theorem node25_29 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node25_27 node27_29
private theorem node21_29 :
    CellBound eighth nn0 nn1 Qcell ((4557:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node21_25 node25_29
private theorem node14_29 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node14_21 node21_29
private theorem node0_29 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_14 node14_29
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_29
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28]
theorem packet_count : packets.length = 29 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC01
#check @N11Formalization.C450EighthGroupedC01.bound
#print axioms N11Formalization.C450EighthGroupedC01.valid0
#print axioms N11Formalization.C450EighthGroupedC01.valid1
#print axioms N11Formalization.C450EighthGroupedC01.valid2
#print axioms N11Formalization.C450EighthGroupedC01.valid3
#print axioms N11Formalization.C450EighthGroupedC01.valid4
#print axioms N11Formalization.C450EighthGroupedC01.valid5
#print axioms N11Formalization.C450EighthGroupedC01.valid6
#print axioms N11Formalization.C450EighthGroupedC01.valid7
#print axioms N11Formalization.C450EighthGroupedC01.valid8
#print axioms N11Formalization.C450EighthGroupedC01.valid9
#print axioms N11Formalization.C450EighthGroupedC01.valid10
#print axioms N11Formalization.C450EighthGroupedC01.valid11
#print axioms N11Formalization.C450EighthGroupedC01.valid12
#print axioms N11Formalization.C450EighthGroupedC01.valid13
#print axioms N11Formalization.C450EighthGroupedC01.valid14
#print axioms N11Formalization.C450EighthGroupedC01.valid15
#print axioms N11Formalization.C450EighthGroupedC01.valid16
#print axioms N11Formalization.C450EighthGroupedC01.valid17
#print axioms N11Formalization.C450EighthGroupedC01.valid18
#print axioms N11Formalization.C450EighthGroupedC01.valid19
#print axioms N11Formalization.C450EighthGroupedC01.valid20
#print axioms N11Formalization.C450EighthGroupedC01.valid21
#print axioms N11Formalization.C450EighthGroupedC01.valid22
#print axioms N11Formalization.C450EighthGroupedC01.valid23
#print axioms N11Formalization.C450EighthGroupedC01.valid24
#print axioms N11Formalization.C450EighthGroupedC01.valid25
#print axioms N11Formalization.C450EighthGroupedC01.valid26
#print axioms N11Formalization.C450EighthGroupedC01.valid27
#print axioms N11Formalization.C450EighthGroupedC01.valid28
#print axioms N11Formalization.C450EighthGroupedC01.bound
#print axioms N11Formalization.C450EighthGroupedC01.endpoint_checks
