import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((6887891399:ℚ)/10000000000),((3549742627:ℚ)/5000000000),((-9369227881:ℚ)/9920000000),((-41495239793:ℚ)/50550000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4363471897:ℚ)/10000000000),((756491587964817660979849896322942305699301:ℚ)/4190968665600000000000000000000000000000000),((295708157031878335521206767:ℚ)/369664000000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((4063:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((437929337:ℚ)/625000000),((3564602211:ℚ)/5000000000),((-9413806633:ℚ)/10110000000),((-2645505359:ℚ)/3174218750),((4956442379:ℚ)/5000000000),((2482425353:ℚ)/2500000000),((1320924081:ℚ)/10000000000),((3976941139:ℚ)/10000000000),((559484954494841749274328151897730206071824996960007729565639:ℚ)/3331786394893308398437500000000000000000000000000000000000000),((296119016907414446517315183:ℚ)/369664000000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4063:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((4063:ℚ)/6400),((2041:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((3518306277:ℚ)/5000000000),((3579461647:ℚ)/5000000000),((-9458384941:ℚ)/10157500000),((-21268143939:ℚ)/25512500000),((247409071:ℚ)/250000000),((9912884763:ℚ)/10000000000),((1440948769:ℚ)/10000000000),((387464449:ℚ)/1000000000),((40650629201382698634713649719815156006295965704314752670321:ℚ)/242175984665112744140625000000000000000000000000000000000000),((296530126713833540611606807:ℚ)/369664000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((4063:ℚ)/6400) ((2041:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((1766588799:ℚ)/2500000000),((1797160469:ℚ)/2500000000),((-4751481407:ℚ)/5102500000),((-3562040531:ℚ)/4271875000),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((753943703:ℚ)/2000000000),((1201537952486574611449583577314830805262199046418747653599:ℚ)/7161005127930544921875000000000000000000000000000000000000),((74235371631655530132466303:ℚ)/92416000000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4101:ℚ)/6400),((8221:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((3548048663:ℚ)/5000000000),((7203501059:ℚ)/10000000000),((-19050503177:ℚ)/20505000000),((-21476340641:ℚ)/25690625000),((4936061823:ℚ)/5000000000),((9880131563:ℚ)/10000000000),((320187229:ℚ)/2000000000),((3661936689:ℚ)/10000000000),((301829895242133930172427155682981415804494229158316867757831799:ℚ)/1820868734942874664453125000000000000000000000000000000000000000),((1188589040773875713040665263:ℚ)/1478656000000000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((4101:ℚ)/6400) ((8221:ℚ)/12800) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((8221:ℚ)/12800),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((7110968201:ℚ)/10000000000),((721836017:ℚ)/1000000000),((-1909508051:ℚ)/2055250000),((-43056777407:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((9872123651:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((3606894931:ℚ)/10000000000),((47701723878490689563415318010234519306299530500923212313:ℚ)/287818325201530712890625000000000000000000000000000000000),((11894123854642130486791447:ℚ)/14786560000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((8221:ℚ)/12800) ((103:ℚ)/160) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((103:ℚ)/160),((8259:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7125838951:ℚ)/10000000000),((7233219211:ℚ)/10000000000),((-19139657633:ℚ)/20600000000),((-43160872657:ℚ)/51618750000),((9856320801:ℚ)/10000000000),((616511681:ℚ)/625000000),((1697201141:ℚ)/10000000000),((3551038451:ℚ)/10000000000),((402062426816619186852633749156269220063769845088893213045773:ℚ)/2426305010022363281250000000000000000000000000000000000000000),((1190235980284679519729717183:ℚ)/1478656000000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((8259:ℚ)/12800) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((8259:ℚ)/12800),((4139:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((892588697:ℚ)/1250000000),((3624039091:ℚ)/5000000000),((-9592117273:ℚ)/10323750000),((-5408120879:ℚ)/6467187500),((984852489:ℚ)/1000000000),((4928160403:ℚ)/5000000000),((1742751127:ℚ)/10000000000),((873582029:ℚ)/2500000000),((2439912858948280160480383167626274801401943818767221928645991:ℚ)/14726289046257507719421386718750000000000000000000000000000000),((297764956307921319023275663:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((8259:ℚ)/12800) ((4139:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4139:ℚ)/6400),((8297:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7155580077:ℚ)/10000000000),((3631468541:ℚ)/5000000000),((-9614405623:ℚ)/10347500000),((-43369060539:ℚ)/51856250000),((9840798677:ℚ)/10000000000),((1969704979:ℚ)/2000000000),((1786759881:ℚ)/10000000000),((343672159:ℚ)/1000000000),((1579329788966815822700213583179824175288081643253916050066561:ℚ)/9533634510074848380859375000000000000000000000000000000000000),((297970980061542640776690863:ℚ)/369664000000000000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((4139:ℚ)/6400) ((8297:ℚ)/12800) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8297:ℚ)/12800),((16613:ℚ)/25600),((-15:ℚ)/16),((-7:ℚ)/8),((1434090091:ℚ)/2000000000),((7270366507:ℚ)/10000000000),((-19251099521:ℚ)/20742500000),((-8694630637:ℚ)/10383125000),((9836961557:ℚ)/10000000000),((4920399341:ℚ)/5000000000),((1808222361:ℚ)/10000000000),((844543239:ℚ)/2500000000),((316868009249321174545555272745946976394665521342742450004396303:ℚ)/1924285275962023500207519531250000000000000000000000000000000000),((1192296061617732697969148927:ℚ)/1478656000000000000000000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((8297:ℚ)/12800) ((16613:ℚ)/25600) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((16613:ℚ)/25600),((2079:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7177885599:ℚ)/10000000000),((3638897957:ℚ)/5000000000),((-9636693871:ℚ)/10383125000),((-2072628533:ℚ)/2475000000),((4916570841:ℚ)/5000000000),((4918480781:ℚ)/5000000000),((1829340989:ℚ)/10000000000),((3348529913:ℚ)/10000000000),((156813036451769199602575891367515111595657350300307710333:ℚ)/952362217024675941467285156250000000000000000000000000000),((298177066372738832229743327:ℚ)/369664000000000000000000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell ((16613:ℚ)/25600) ((2079:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2079:ℚ)/3200),((16651:ℚ)/25600),((-15:ℚ)/16),((-7:ℚ)/8),((898165089:ℚ)/1250000000),((910653163:ℚ)/1250000000),((-2411959489:ℚ)/2598750000),((-5447155623:ℚ)/6504296875),((4914669497:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((92506391:ℚ)/500000000),((3318632279:ℚ)/10000000000),((10838354621347256429070918691340230320797580119748530262817:ℚ)/65828231903871881103515625000000000000000000000000000000000),((18642508311263632401893887:ℚ)/23104000000000000000000000)⟩
theorem valid11 : Valid source22 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source22 nn0 nn1 Qcell ((2079:ℚ)/3200) ((16651:ℚ)/25600) :=
  cell_of_packet source22 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((16651:ℚ)/25600),((1667:ℚ)/2560),((-15:ℚ)/16),((-7:ℚ)/8),((3596377897:ℚ)/5000000000),((1823163669:ℚ)/2500000000),((-4829491007:ℚ)/5203437500),((-21814645279:ℚ)/26046875000),((4912776717:ℚ)/5000000000),((9829338999:ℚ)/10000000000),((935297099:ℚ)/5000000000),((205529569:ℚ)/625000000),((604276797541696781479124291178160035258621855336405785399767:ℚ)/3670400906921572763156890869140625000000000000000000000000000),((74595803803221507481343103:ℚ)/92416000000000000000000000)⟩
theorem valid12 : Valid source22 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source22 nn0 nn1 Qcell ((16651:ℚ)/25600) ((1667:ℚ)/2560) :=
  cell_of_packet source22 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1667:ℚ)/2560),((16689:ℚ)/25600),((-15:ℚ)/16),((-7:ℚ)/8),((7200190847:ℚ)/10000000000),((114063813:ℚ)/156250000),((-604382878:ℚ)/651171875),((-43681335929:ℚ)/52153125000),((4910892471:ℚ)/5000000000),((9825553439:ℚ)/10000000000),((945375407:ℚ)/5000000000),((3258045107:ℚ)/10000000000),((8791820140933877864044419218111889541563511861385869590497:ℚ)/53405383835104907676577568054199218750000000000000000000000),((291490540135140145995087:ℚ)/361000000000000000000000)⟩
theorem valid13 : Valid source22 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source22 nn0 nn1 Qcell ((1667:ℚ)/2560) ((16689:ℚ)/25600) :=
  cell_of_packet source22 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((16689:ℚ)/25600),((4177:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7207625869:ℚ)/10000000000),((730751337:ℚ)/1000000000),((-1936254011:ℚ)/2086125000),((-43733381083:ℚ)/52212500000),((4909016731:ℚ)/5000000000),((9821784947:ℚ)/10000000000),((382121547:ℚ)/2000000000),((645468137:ℚ)/2000000000),((27160882839411757632379104866707056880896986626544097916279:ℚ)/164998007784543876141357421875000000000000000000000000000000),((11943577064353895609302887:ℚ)/14786560000000000000000000)⟩
theorem valid14 : Valid source22 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source22 nn0 nn1 Qcell ((16689:ℚ)/25600) ((4177:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4177:ℚ)/6400),((16727:ℚ)/25600),((-15:ℚ)/16),((-7:ℚ)/8),((3607530431:ℚ)/5000000000),((1828735673:ℚ)/2500000000),((-4846207019:ℚ)/5221250000),((-21892713017:ℚ)/26135937500),((1962859787:ℚ)/2000000000),((9818033467:ℚ)/10000000000),((482543621:ℚ)/2500000000),((639270371:ℚ)/2000000000),((20485487239050254181114724948965926792627928250455050214481253:ℚ)/124454212273202247662353515625000000000000000000000000000000000),((74673138942981790620308167:ℚ)/92416000000000000000000000)⟩
theorem valid15 : Valid source22 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source22 nn0 nn1 Qcell ((4177:ℚ)/6400) ((16727:ℚ)/25600) :=
  cell_of_packet source22 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((16727:ℚ)/25600),((8373:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((451405989:ℚ)/625000000),((1830592999:ℚ)/2500000000),((-4851778997:ℚ)/5227187500),((-913280641:ℚ)/1090234375),((4905290651:ℚ)/5000000000),((490714947:ℚ)/500000000),((194946007:ℚ)/1000000000),((3165070263:ℚ)/10000000000),((2321168049470364448051114036997504813997014389551246493:ℚ)/14102570602826304674148559570312500000000000000000000000),((74698925139937778193097223:ℚ)/92416000000000000000000000)⟩
theorem valid16 : Valid source22 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source22 nn0 nn1 Qcell ((16727:ℚ)/25600) ((8373:ℚ)/12800) :=
  cell_of_packet source22 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((8373:ℚ)/12800),((1049:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((7229930757:ℚ)/10000000000),((1467446111:ℚ)/2000000000),((-3890338333:ℚ)/4186500000),((-43889515299:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((9810581307:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((783371781:ℚ)/2500000000),((125303396233028634499531196606507831420078835356303755064873:ℚ)/756964546912661621484375000000000000000000000000000000000000),((47840325932578279868998583:ℚ)/59146240000000000000000000)⟩
theorem valid17 : Valid source22 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source22 nn0 nn1 Qcell ((8373:ℚ)/12800) ((1049:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1049:ℚ)/1600),((8411:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((3622400267:ℚ)/5000000000),((7352089047:ℚ)/10000000000),((-19496267141:ℚ)/20980000000),((-21996801869:ℚ)/26284375000),((9795878581:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((1011977397:ℚ)/5000000000),((383672357:ℚ)/1250000000),((337897409591933557276040755194943637028201155482611244355125587:ℚ)/2041558078054343225000000000000000000000000000000000000000000000),((1196833744658311309913285607:ℚ)/1478656000000000000000000000)⟩
theorem valid18 : Valid source22 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source22 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8411:ℚ)/12800) :=
  cell_of_packet source22 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((8411:ℚ)/12800),((843:ℚ)/1280),((-15:ℚ)/16),((-7:ℚ)/8),((7259670193:ℚ)/10000000000),((460434217:ℚ)/625000000),((-1221302651:ℚ)/1314218750),((-44097691351:ℚ)/52687500000),((978862711:ℚ)/1000000000),((4897939293:ℚ)/5000000000),((2059717253:ℚ)/10000000000),((1501973681:ℚ)/5000000000),((834194818750223714602748917583852664316949158502234819453:ℚ)/5040900763706262338161468505859375000000000000000000000000),((4678357778387232493063847:ℚ)/5776000000000000000000000)⟩
theorem valid19 : Valid source22 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source22 nn0 nn1 Qcell ((8411:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_of_packet source22 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((843:ℚ)/1280),((8449:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((1454907947:ℚ)/2000000000),((7381805831:ℚ)/10000000000),((-19585417493:ℚ)/21075000000),((-1262907947:ℚ)/1508750000),((4890720817:ℚ)/5000000000),((1957725423:ℚ)/2000000000),((83782417:ℚ)/400000000),((1468552067:ℚ)/5000000000),((846144443574712025826037609847665022489249914809906398142937:ℚ)/5113856743686580078125000000000000000000000000000000000000000),((1198485688193088438271500103:ℚ)/1478656000000000000000000000)⟩
theorem valid20 : Valid source22 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source22 nn0 nn1 Qcell ((843:ℚ)/1280) ((8449:ℚ)/12800) :=
  cell_of_packet source22 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((8449:ℚ)/12800),((2117:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((182235229:ℚ)/250000000),((1849166031:ℚ)/2500000000),((-4907498093:ℚ)/5280625000),((-1107646603:ℚ)/1323125000),((9774321709:ℚ)/10000000000),((9781441639:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1434375207:ℚ)/5000000000),((20069277765616441429622466006656556960286004201491848613043:ℚ)/121310613397036920928955078125000000000000000000000000000000),((74957002214549844349905303:ℚ)/92416000000000000000000000)⟩
theorem valid21 : Valid source22 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source22 nn0 nn1 Qcell ((8449:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((730427847:ℚ)/1000000000),((1856595129:ℚ)/2500000000),((-4929785387:ℚ)/5292500000),((-4440994929:ℚ)/5316250000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((349846931:ℚ)/1250000000),((1051346152457801750406735682624966375621736633542052595212383:ℚ)/6284701433992841198730468750000000000000000000000000000000000),((75060342566410359794015943:ℚ)/92416000000000000000000000)⟩
theorem valid22 : Valid source22 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source22 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((3667008373:ℚ)/5000000000),((149121933:ℚ)/200000000),((-396165799:ℚ)/425300000),((-22309058611:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((2653445477:ℚ)/10000000000),((179120844441374608319485757872076685437135380451397917:ℚ)/1071121433793955664062500000000000000000000000000000000),((481047971296461840172047:ℚ)/591462400000000000000000)⟩
theorem valid23 : Valid source22 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source22 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-15:ℚ)/16),((-7:ℚ)/8),((736375457:ℚ)/1000000000),((46972051:ℚ)/62500000),((-124916153:ℚ)/133500000),((-4482628199:ℚ)/5387500000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((499978551:ℚ)/2000000000),((707966079594795490617269549759954872444029011181167893:ℚ)/4143521663722265625000000000000000000000000000000000000),((47106712032465631767023:ℚ)/57760000000000000000000)⟩
theorem valid24 : Valid source22 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source22 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((7423228883:ℚ)/10000000000),((7574958681:ℚ)/10000000000),((-20164876043:ℚ)/21550000000),((-45242602181:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2161022319:ℚ)/10000000000),((6307910706256230181276390168820392052020538413692877847472981:ℚ)/36953104770655859375000000000000000000000000000000000000000000),((1209247736101674014891501703:ℚ)/1478656000000000000000000000)⟩
theorem valid25 : Valid source22 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source22 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((1496540291:ℚ)/2000000000),((7693816857:ℚ)/10000000000),((-20521450571:ℚ)/21740000000),((-1304540291:ℚ)/1580000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1759197819:ℚ)/10000000000),((6677647304343264923868924223545762892900974186755732085631:ℚ)/37573711426045312500000000000000000000000000000000000000000),((419198797:ℚ)/512000000)⟩
theorem valid26 : Valid source22 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source22 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((7601641559:ℚ)/10000000000),((495720151:ℚ)/625000000),((-1327160453:ℚ)/1382500000),((-46491490913:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((4611713666213776238602141594750297300157611803072342843:ℚ)/24122342335888671875000000000000000000000000000000000000),((419198797:ℚ)/512000000)⟩
theorem valid27 : Valid source22 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((7839502781:ℚ)/10000000000),((8882223979:ℚ)/10000000000),(-1:ℚ),((-48156519467:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((5001161421327843980618314565532677959:ℚ)/20995200000000000000000000000000000000),((419198797:ℚ)/512000000)⟩
theorem valid28 : Valid source22 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((109884193:ℚ)/125000000),((5391613451:ℚ)/5000000000),(-1:ℚ),((-685189351:ℚ)/1000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((956591187821773089211920991389857:ℚ)/3750000000000000000000000000000000),((419198797:ℚ)/512000000)⟩
theorem valid29 : Valid source22 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet29 valid29
def packet30 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((10692497183:ℚ)/10000000000),((14584403867:ℚ)/10000000000),(-1:ℚ),((-68127480281:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1737863196294036897263750329:ℚ)/6094080000000000000000000000),((419198797:ℚ)/512000000)⟩
theorem valid30 : Valid source22 packet30 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf30 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet30 valid30
private theorem node1_3 :
    CellBound source22 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source22 nn0 nn1 Qcell ((2041:ℚ)/3200) ((8221:ℚ)/12800) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source22 nn0 nn1 Qcell ((8221:ℚ)/12800) ((8259:ℚ)/12800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source22 nn0 nn1 Qcell ((2041:ℚ)/3200) ((8259:ℚ)/12800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((8259:ℚ)/12800) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source22 nn0 nn1 Qcell ((8259:ℚ)/12800) ((8297:ℚ)/12800) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source22 nn0 nn1 Qcell ((8297:ℚ)/12800) ((2079:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source22 nn0 nn1 Qcell ((8259:ℚ)/12800) ((2079:ℚ)/3200) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source22 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1667:ℚ)/2560) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source22 nn0 nn1 Qcell ((1667:ℚ)/2560) ((4177:ℚ)/6400) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source22 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source22 nn0 nn1 Qcell ((8259:ℚ)/12800) ((4177:ℚ)/6400) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((4177:ℚ)/6400) :=
  cell_join node0_7 node7_15
private theorem node15_17 :
    CellBound source22 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8373:ℚ)/12800) :=
  cell_join leaf15 leaf16
private theorem node17_19 :
    CellBound source22 nn0 nn1 Qcell ((8373:ℚ)/12800) ((8411:ℚ)/12800) :=
  cell_join leaf17 leaf18
private theorem node15_19 :
    CellBound source22 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8411:ℚ)/12800) :=
  cell_join node15_17 node17_19
private theorem node19_21 :
    CellBound source22 nn0 nn1 Qcell ((8411:ℚ)/12800) ((8449:ℚ)/12800) :=
  cell_join leaf19 leaf20
private theorem node21_23 :
    CellBound source22 nn0 nn1 Qcell ((8449:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_join leaf21 leaf22
private theorem node19_23 :
    CellBound source22 nn0 nn1 Qcell ((8411:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_join node19_21 node21_23
private theorem node15_23 :
    CellBound source22 nn0 nn1 Qcell ((4177:ℚ)/6400) ((4253:ℚ)/6400) :=
  cell_join node15_19 node19_23
private theorem node23_25 :
    CellBound source22 nn0 nn1 Qcell ((4253:ℚ)/6400) ((431:ℚ)/640) :=
  cell_join leaf23 leaf24
private theorem node25_27 :
    CellBound source22 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf25 leaf26
private theorem node23_27 :
    CellBound source22 nn0 nn1 Qcell ((4253:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join node23_25 node25_27
private theorem node27_29 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf27 leaf28
private theorem node29_31 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf29 leaf30
private theorem node27_31 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node27_29 node29_31
private theorem node23_31 :
    CellBound source22 nn0 nn1 Qcell ((4253:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node23_27 node27_31
private theorem node15_31 :
    CellBound source22 nn0 nn1 Qcell ((4177:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node15_23 node23_31
private theorem node0_31 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_15 node15_31
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_31
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29,packet30]
theorem packet_count : packets.length = 31 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC02
#check @N11Formalization.C450Source22GroupedC02.bound
#print axioms N11Formalization.C450Source22GroupedC02.valid0
#print axioms N11Formalization.C450Source22GroupedC02.valid1
#print axioms N11Formalization.C450Source22GroupedC02.valid2
#print axioms N11Formalization.C450Source22GroupedC02.valid3
#print axioms N11Formalization.C450Source22GroupedC02.valid4
#print axioms N11Formalization.C450Source22GroupedC02.valid5
#print axioms N11Formalization.C450Source22GroupedC02.valid6
#print axioms N11Formalization.C450Source22GroupedC02.valid7
#print axioms N11Formalization.C450Source22GroupedC02.valid8
#print axioms N11Formalization.C450Source22GroupedC02.valid9
#print axioms N11Formalization.C450Source22GroupedC02.valid10
#print axioms N11Formalization.C450Source22GroupedC02.valid11
#print axioms N11Formalization.C450Source22GroupedC02.valid12
#print axioms N11Formalization.C450Source22GroupedC02.valid13
#print axioms N11Formalization.C450Source22GroupedC02.valid14
#print axioms N11Formalization.C450Source22GroupedC02.valid15
#print axioms N11Formalization.C450Source22GroupedC02.valid16
#print axioms N11Formalization.C450Source22GroupedC02.valid17
#print axioms N11Formalization.C450Source22GroupedC02.valid18
#print axioms N11Formalization.C450Source22GroupedC02.valid19
#print axioms N11Formalization.C450Source22GroupedC02.valid20
#print axioms N11Formalization.C450Source22GroupedC02.valid21
#print axioms N11Formalization.C450Source22GroupedC02.valid22
#print axioms N11Formalization.C450Source22GroupedC02.valid23
#print axioms N11Formalization.C450Source22GroupedC02.valid24
#print axioms N11Formalization.C450Source22GroupedC02.valid25
#print axioms N11Formalization.C450Source22GroupedC02.valid26
#print axioms N11Formalization.C450Source22GroupedC02.valid27
#print axioms N11Formalization.C450Source22GroupedC02.valid28
#print axioms N11Formalization.C450Source22GroupedC02.valid29
#print axioms N11Formalization.C450Source22GroupedC02.valid30
#print axioms N11Formalization.C450Source22GroupedC02.bound
#print axioms N11Formalization.C450Source22GroupedC02.endpoint_checks
