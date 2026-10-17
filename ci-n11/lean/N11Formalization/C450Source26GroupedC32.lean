import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((15:ℚ)/16),(1:ℚ),((2599999999:ℚ)/5000000000),((2764413099:ℚ)/5000000000),((9335999997:ℚ)/10300000000),(1:ℚ),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2043189277:ℚ)/2500000000),((-3097768208184857718302121667250417853016568534610735717:ℚ)/6829543750000000000000000000000000000000000000000000000),((-5042288411531287113638577:ℚ)/14786560000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((2718749999:ℚ)/5000000000),((5766635211:ℚ)/10000000000),((3230749999:ℚ)/3560000000),(1:ℚ),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((3867566401:ℚ)/5000000000),((-31961508553550292864288497373277420539150821409765951:ℚ)/70496900000000000000000000000000000000000000000000000),((-4880133951878880497738577:ℚ)/14786560000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((2837499999:ℚ)/5000000000),((14713829:ℚ)/25000000),((10048499997:ℚ)/10870000000),(1:ℚ),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7276935417:ℚ)/10000000000),((-3818630336719675583430566641248268843966247732511441677:ℚ)/8027284393750000000000000000000000000000000000000000000),((-4812333727504482645038577:ℚ)/14786560000000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2896874999:ℚ)/5000000000),((5944977889:ℚ)/10000000000),((3408874999:ℚ)/3655000000),(1:ℚ),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((7038820797:ℚ)/10000000000),((-37130481301856620754926814952425723186543452054105231:ℚ)/76292556835937500000000000000000000000000000000000000),((-4778843106832587616088577:ℚ)/14786560000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((2926562499:ℚ)/5000000000),((6004422951:ℚ)/10000000000),((10315687497:ℚ)/11060000000),(1:ℚ),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6917231431:ℚ)/10000000000),((-64247121025470239101047239761156636038484936463809113:ℚ)/132119044531250000000000000000000000000000000000000000),((-4738888127927757506363577:ℚ)/14786560000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2956249999:ℚ)/5000000000),((6063866817:ℚ)/10000000000),((10404749997:ℚ)/11155000000),(1:ℚ),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((6793830161:ℚ)/10000000000),((-263458052349297875526771599996204830532409142324907293:ℚ)/542211542529296875000000000000000000000000000000000000),((-4699002086573698521938577:ℚ)/14786560000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((15:ℚ)/16),(1:ℚ),((2985937499:ℚ)/5000000000),((6123309519:ℚ)/10000000000),((3497937499:ℚ)/3750000000),(1:ℚ),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1333702761:ℚ)/2000000000),((-1875281948975524748939690055356736130850609146192793:ℚ)/3862380981445312500000000000000000000000000000000000),((-4659184957671983885213577:ℚ)/14786560000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3015624999:ℚ)/5000000000),((3076515221:ℚ)/5000000000),((10582874997:ℚ)/11297500000),(1:ℚ),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((6541169681:ℚ)/10000000000),((-4423158176584488186499790861619332879119882972013309413:ℚ)/9012122105371093750000000000000000000000000000000000000),((-4642747387452699228188577:ℚ)/14786560000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3030468749:ℚ)/5000000000),((1236550217:ℚ)/2000000000),((10627406247:ℚ)/11345000000),(1:ℚ),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((1295339817:ℚ)/2000000000),((-11193262172752393771883296767560847661186798527097943:ℚ)/22815685759765625000000000000000000000000000000000000),((-4622898877864470887663577:ℚ)/14786560000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3045312499:ℚ)/5000000000),((124249429:ℚ)/200000000),((3557312499:ℚ)/3797500000),(1:ℚ),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((801459291:ℚ)/1250000000),((-167848694663509239547875379999483383433870268923930579:ℚ)/342273570214843750000000000000000000000000000000000000),((-4603067586193092755663577:ℚ)/14786560000000000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3060156249:ℚ)/5000000000),((6242191543:ℚ)/10000000000),((10716468747:ℚ)/11440000000),(1:ℚ),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((198314939:ℚ)/312500000),((-416999105941247109864142984456344763096295402746476457:ℚ)/850678400000000000000000000000000000000000000000000000),((-4583253507732609811388577:ℚ)/14786560000000000000000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((15:ℚ)/16),(1:ℚ),((3074999999:ℚ)/5000000000),((1254382273:ℚ)/2000000000),((10760999997:ℚ)/11487500000),(1:ℚ),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((3139946003:ℚ)/5000000000),((-4642533430478089555730462438641705624714746753072267213:ℚ)/9474506335449218750000000000000000000000000000000000000),((-4563456641698696218038577:ℚ)/14786560000000000000000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3089843749:ℚ)/5000000000),((6301630921:ℚ)/10000000000),((3601843749:ℚ)/3845000000),(1:ℚ),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((6213097021:ℚ)/10000000000),((-6797666216553922395262298176020378450296303095989:ℚ)/13878070343017578125000000000000000000000000000000),((-4543676984169722791613577:ℚ)/14786560000000000000000000)⟩
theorem valid12 : Valid source26 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source26 nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2307:ℚ)/3200),((9247:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((3104687499:ℚ)/5000000000),((31582453:ℚ)/50000000),((10850062497:ℚ)/11558750000),(1:ℚ),((4766928483:ℚ)/5000000000),((1907725537:ℚ)/2000000000),((3065322907:ℚ)/10000000000),((768209113:ℚ)/1250000000),((-1188093901239442563477022878454727304454501607452735473:ℚ)/2412973975289916992187500000000000000000000000000000000),((-4535569311977787016913577:ℚ)/14786560000000000000000000)⟩
theorem valid13 : Valid source26 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source26 nn0 nn1 Qcell ((2307:ℚ)/3200) ((9247:ℚ)/12800) :=
  cell_of_packet source26 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((9247:ℚ)/12800),((4633:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((1556054687:ℚ)/2500000000),((3165675107:ℚ)/5000000000),((5436164061:ℚ)/5791250000),(1:ℚ),((1905827251:ℚ)/2000000000),((9533856971:ℚ)/10000000000),((3080928657:ℚ)/10000000000),((3055859159:ℚ)/5000000000),((-23903832894701232235189502131182378274068243722021429:ℚ)/48557570379394531250000000000000000000000000000000000),((-1131423621683180417440113:ℚ)/3696640000000000000000000)⟩
theorem valid14 : Valid source26 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source26 nn0 nn1 Qcell ((9247:ℚ)/12800) ((4633:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4633:ℚ)/6400),((1857:ℚ)/2560),((15:ℚ)/16),(1:ℚ),((3119531249:ℚ)/5000000000),((3173104881:ℚ)/5000000000),((5866771:ℚ)/6250000),(1:ℚ),((9524465239:ℚ)/10000000000),((476456813:ℚ)/500000000),((3096295161:ℚ)/10000000000),((6077598383:ℚ)/10000000000),((-751007092794310463588242752564157666436490579:ℚ)/1525878906250000000000000000000000000000000000),((-4515823963221728445938577:ℚ)/14786560000000000000000000)⟩
theorem valid15 : Valid source26 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source26 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1857:ℚ)/2560) :=
  cell_of_packet source26 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1857:ℚ)/2560),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((781738281:ℚ)/1250000000),((3180534623:ℚ)/5000000000),((2729214843:ℚ)/2907500000),(1:ℚ),((9519843613:ℚ)/10000000000),((2381116311:ℚ)/2500000000),((622285377:ℚ)/2000000000),((1208662051:ℚ)/2000000000),((-75592277623281897498898311903270738193792858706591347:ℚ)/153616967480468750000000000000000000000000000000000000),((-281622358742259729490497:ℚ)/924160000000000000000000)⟩
theorem valid16 : Valid source26 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source26 nn0 nn1 Qcell ((1857:ℚ)/2560) ((1163:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((1163:ℚ)/1600),((9323:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((3134374999:ℚ)/5000000000),((3187964333:ℚ)/5000000000),((10939124997:ℚ)/11653750000),(1:ℚ),((2378817769:ℚ)/2500000000),((4759921809:ℚ)/5000000000),((156316407:ℚ)/500000000),((6008851013:ℚ)/10000000000),((-304165910748099987796637896882698807449425058620065077:ℚ)/618240036977386474609375000000000000000000000000000000),((-4496095816696003347488577:ℚ)/14786560000000000000000000)⟩
theorem valid17 : Valid source26 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((9323:ℚ)/12800) :=
  cell_of_packet source26 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((9323:ℚ)/12800),((4671:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((1570898437:ℚ)/2500000000),((3195394011:ℚ)/5000000000),((1826898437:ℚ)/1946250000),(1:ℚ),((148605427:ℚ)/156250000),((9515271081:ℚ)/10000000000),((98156347:ℚ)/312500000),((2987108827:ℚ)/5000000000),((-5533315296610805168684990533299181536700797939533:ℚ)/11249052563309669494628906250000000000000000000000),((-1121559548420317868215113:ℚ)/3696640000000000000000000)⟩
theorem valid18 : Valid source26 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source26 nn0 nn1 Qcell ((9323:ℚ)/12800) ((4671:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((4671:ℚ)/6400),((9361:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((3149218749:ℚ)/5000000000),((3202823657:ℚ)/5000000000),((10983656247:ℚ)/11701250000),(1:ℚ),((1188284009:ℚ)/1250000000),((9510747333:ℚ)/10000000000),((157772791:ℚ)/500000000),((5939407091:ℚ)/10000000000),((-6995045559707468768779449652486984042961984544976397:ℚ)/14223423227500915527343750000000000000000000000000000),((-4476384870831960047963577:ℚ)/14786560000000000000000000)⟩
theorem valid19 : Valid source26 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source26 nn0 nn1 Qcell ((4671:ℚ)/6400) ((9361:ℚ)/12800) :=
  cell_of_packet source26 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((9361:ℚ)/12800),((469:ℚ)/640),((15:ℚ)/16),(1:ℚ),((197290039:ℚ)/312500000),((6420506543:ℚ)/10000000000),((687870117:ℚ)/732812500),(1:ℚ),((9501845013:ℚ)/10000000000),((9506272077:ℚ)/10000000000),((792422551:ℚ)/2500000000),((2952208073:ℚ)/5000000000),((-1209380215518267214210934089128191783783603520587073:ℚ)/2459566807746887207031250000000000000000000000000000),((-17447405653764622015617:ℚ)/57760000000000000000000)⟩
theorem valid20 : Valid source26 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source26 nn0 nn1 Qcell ((9361:ℚ)/12800) ((469:ℚ)/640) :=
  cell_of_packet source26 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((469:ℚ)/640),((9399:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((3164062499:ℚ)/5000000000),((643536571:ℚ)/1000000000),((3676062499:ℚ)/3916250000),(1:ℚ),((474873293:ℚ)/500000000),((4750922509:ℚ)/5000000000),((636742009:ℚ)/2000000000),((5869241551:ℚ)/10000000000),((-1914419626768066791855351951630541024495728664699:ℚ)/3894163726806640625000000000000000000000000000000),((-4456691122492295200163577:ℚ)/14786560000000000000000000)⟩
theorem valid21 : Valid source26 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source26 nn0 nn1 Qcell ((469:ℚ)/640) ((9399:ℚ)/12800) :=
  cell_of_packet source26 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((9399:ℚ)/12800),((4709:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((1585742187:ℚ)/2500000000),((3225112407:ℚ)/5000000000),((5525226561:ℚ)/5886250000),(1:ℚ),((9493134321:ℚ)/10000000000),((1899493173:ℚ)/2000000000),((1598759513:ℚ)/5000000000),((5833879941:ℚ)/10000000000),((-36854430111116048173524041887710759603675092981835417:ℚ)/74980305627441406250000000000000000000000000000000000),((-1111712674250485444315113:ℚ)/3696640000000000000000000)⟩
theorem valid22 : Valid source26 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source26 nn0 nn1 Qcell ((9399:ℚ)/12800) ((4709:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((4709:ℚ)/6400),((9437:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((3178906249:ℚ)/5000000000),((6465083857:ℚ)/10000000000),((11072718747:ℚ)/11796250000),(1:ℚ),((948885011:ℚ)/1000000000),((4746567163:ℚ)/5000000000),((802780177:ℚ)/2500000000),((1449581963:ℚ)/2500000000),((-50416749312000849384277695338392452462655868406556147:ℚ)/102591627984985351562500000000000000000000000000000000),((-4437014569324031293688577:ℚ)/14786560000000000000000000)⟩
theorem valid23 : Valid source26 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source26 nn0 nn1 Qcell ((4709:ℚ)/6400) ((9437:ℚ)/12800) :=
  cell_of_packet source26 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((9437:ℚ)/12800),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((796582031:ℚ)/1250000000),((3239971419:ℚ)/5000000000),((924582031:ℚ)/985000000),(1:ℚ),((4742306471:ℚ)/5000000000),((1897770023:ℚ)/2000000000),((806129637:ℚ)/2500000000),((1440645429:ℚ)/2500000000),((-733690539583843544454722125572624353997493704386679:ℚ)/1493236914062500000000000000000000000000000000000000),((-276698921265180599140497:ℚ)/924160000000000000000000)⟩
theorem valid24 : Valid source26 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source26 nn0 nn1 Qcell ((9437:ℚ)/12800) ((591:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3193749999:ℚ)/5000000000),((813707577:ℚ)/1250000000),((11117249997:ℚ)/11867500000),(1:ℚ),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((2863318927:ℚ)/5000000000),((-5104003857489230437962536500911203630811085895305210957:ℚ)/10446185617480468750000000000000000000000000000000000000),((-4405701022739448443738577:ℚ)/14786560000000000000000000)⟩
theorem valid25 : Valid source26 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3208593749:ℚ)/5000000000),((6539378153:ℚ)/10000000000),((11161781247:ℚ)/11915000000),(1:ℚ),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((70676771:ℚ)/125000000),((-5163863580621595849601963402662425480127292868843814983:ℚ)/10572121786718750000000000000000000000000000000000000000),((-4386058947758480141513577:ℚ)/14786560000000000000000000)⟩
theorem valid26 : Valid source26 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source26 nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((2383:ℚ)/3200),((957:ℚ)/1280),((15:ℚ)/16),(1:ℚ),((3223437499:ℚ)/5000000000),((6569095451:ℚ)/10000000000),((3735437499:ℚ)/3987500000),(1:ℚ),((75681297:ℚ)/80000000),((2367032267:ℚ)/2500000000),((1650403157:ℚ)/5000000000),((5580807559:ℚ)/10000000000),((-1125756713156248531271960102371052993070598846929:ℚ)/2305522656250000000000000000000000000000000000000),((-4366434060105654412613577:ℚ)/14786560000000000000000000)⟩
theorem valid27 : Valid source26 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source26 nn0 nn1 Qcell ((2383:ℚ)/3200) ((957:ℚ)/1280) :=
  cell_of_packet source26 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((957:ℚ)/1280),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3238281249:ℚ)/5000000000),((6598812513:ℚ)/10000000000),((11250843747:ℚ)/12010000000),(1:ℚ),((4726187811:ℚ)/5000000000),((946016213:ℚ)/1000000000),((831186567:ℚ)/2500000000),((5506601661:ℚ)/10000000000),((-1321264935412100833819160271910479586430042358186322347:ℚ)/2706755626562500000000000000000000000000000000000000000),((-4346826357427993746638577:ℚ)/14786560000000000000000000)⟩
theorem valid28 : Valid source26 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source26 nn0 nn1 Qcell ((957:ℚ)/1280) ((1201:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨((1201:ℚ)/1600),((4823:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3253124999:ℚ)/5000000000),((6628529341:ℚ)/10000000000),((11295374997:ℚ)/12057500000),(1:ℚ),((9444767421:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1673989387:ℚ)/5000000000),((678935987:ℚ)/1250000000),((-15587174792840977875827876185870449231897236648842059:ℚ)/31941676660156250000000000000000000000000000000000000),((-4327235838156846469988577:ℚ)/14786560000000000000000000)⟩
theorem valid29 : Valid source26 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source26 nn0 nn1 Qcell ((1201:ℚ)/1600) ((4823:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet29 valid29
def packet30 : Packet := ⟨((4823:ℚ)/6400),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3267968749:ℚ)/5000000000),((6658245939:ℚ)/10000000000),((1259989583:ℚ)/1345000000),(1:ℚ),((4718667711:ℚ)/5000000000),((4722383713:ℚ)/5000000000),((674104879:ℚ)/2000000000),((669428463:ℚ)/1250000000),((-5564033722094289337975707671878213153667164894371829:ℚ)/11405337304687500000000000000000000000000000000000000),((-4307662499154909235463577:ℚ)/14786560000000000000000000)⟩
theorem valid30 : Valid source26 packet30 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf30 :
    CellBound source26 nn0 nn1 Qcell ((4823:ℚ)/6400) ((2421:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet30 valid30
def packet31 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3282812499:ℚ)/5000000000),((1343535691:ℚ)/2000000000),((11384437497:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((164949369:ℚ)/312500000),((-5477370585968055340876921354390291353097347810894988257:ℚ)/11349050000000000000000000000000000000000000000000000000),((-4264799197775609396663577:ℚ)/14786560000000000000000000)⟩
theorem valid31 : Valid source26 packet31 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf31 :
    CellBound source26 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source26 nn0 nn1 packet31 valid31
def packet32 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3312499999:ℚ)/5000000000),((21178469:ℚ)/31250000),((11473499997:ℚ)/12295000000),(1:ℚ),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((5121140523:ℚ)/10000000000),((-350238026450730799071811473862517729732163030442702813:ℚ)/726015067333984375000000000000000000000000000000000000),((-4225738751318962431038577:ℚ)/14786560000000000000000000)⟩
theorem valid32 : Valid source26 packet32 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf32 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet32 valid32
def packet33 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3342187499:ℚ)/5000000000),((1709135209:ℚ)/2500000000),((3854187499:ℚ)/4130000000),(1:ℚ),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((619921757:ℚ)/1250000000),((-212306666485710561637877528529546726382444983688895219:ℚ)/440281231250000000000000000000000000000000000000000000),((-4186746985938537957113577:ℚ)/14786560000000000000000000)⟩
theorem valid33 : Valid source26 packet33 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf33 :
    CellBound source26 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet33 valid33
def packet34 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3371874999:ℚ)/5000000000),((6955399817:ℚ)/10000000000),((11651624997:ℚ)/12580000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((4792618879:ℚ)/10000000000),((-1469473001642358670771070409646719359201927374230352293:ℚ)/3110727362500000000000000000000000000000000000000000000),((-4101212127752520115688577:ℚ)/14786560000000000000000000)⟩
theorem valid34 : Valid source26 packet34 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf34 :
    CellBound source26 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet34 valid34
def packet35 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((3431249999:ℚ)/5000000000),((3596554091:ℚ)/5000000000),((3943249999:ℚ)/4320000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((277616589:ℚ)/625000000),((-76275056166349247842739563877544454388027328239396477:ℚ)/167961600000000000000000000000000000000000000000000000),((-3930353937046751139938577:ℚ)/14786560000000000000000000)⟩
theorem valid35 : Valid source26 packet35 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf35 :
    CellBound source26 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet35 valid35
def packet36 : Packet := ⟨((81:ℚ)/100),((343:ℚ)/400),((15:ℚ)/16),(1:ℚ),((3549999999:ℚ)/5000000000),((7668490243:ℚ)/10000000000),((12185999997:ℚ)/13720000000),(1:ℚ),((57977633:ℚ)/62500000),((2332870371:ℚ)/2500000000),((1913736159:ℚ)/5000000000),((729513699:ℚ)/2000000000),((-266200602752152411135858202387289646174812508277773:ℚ)/630525109375000000000000000000000000000000000000000),((-3643199408546103300038577:ℚ)/14786560000000000000000000)⟩
theorem valid36 : Valid source26 packet36 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf36 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((343:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet36 valid36
def packet37 : Packet := ⟨((343:ℚ)/400),((181:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3787499999:ℚ)/5000000000),((1628766431:ℚ)/2000000000),((12898499997:ℚ)/14480000000),(1:ℚ),((9252071821:ℚ)/10000000000),((1855284257:ℚ)/2000000000),((1946075537:ℚ)/5000000000),((50708103:ℚ)/625000000),((-8066826148808743433323710400967999708721937331046694837:ℚ)/18975171200000000000000000000000000000000000000000000000),((-3710425858684029225038577:ℚ)/14786560000000000000000000)⟩
theorem valid37 : Valid source26 packet37 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf37 :
    CellBound source26 nn0 nn1 Qcell ((343:ℚ)/400) ((181:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet37 valid37
def packet38 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((15:ℚ)/16),(1:ℚ),((4024999999:ℚ)/5000000000),((1818883689:ℚ)/2000000000),((13610999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-2410582912591036474202184897908982232100174046518380557:ℚ)/6400000000000000000000000000000000000000000000000000000),((-128604039:ℚ)/512000000)⟩
theorem valid38 : Valid source26 packet38 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf38 :
    CellBound source26 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet38 valid38
def packet39 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4499999999:ℚ)/5000000000),((3223988983:ℚ)/2500000000),((5011999999:ℚ)/7360000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-18929858930948843924655427891931173:ℚ)/99672064000000000000000000000000000),((-128604039:ℚ)/512000000)⟩
theorem valid39 : Valid source26 packet39 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf39 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet39 valid39
private theorem node0_2 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source26 nn0 nn1 Qcell ((4519:ℚ)/6400) ((4557:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((4557:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((4557:ℚ)/6400) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((4557:ℚ)/6400) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source26 nn0 nn1 Qcell ((4557:ℚ)/6400) ((919:ℚ)/1280) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source26 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source26 nn0 nn1 Qcell ((919:ℚ)/1280) ((4633:ℚ)/6400) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source26 nn0 nn1 Qcell ((4557:ℚ)/6400) ((4633:ℚ)/6400) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound source26 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound source26 nn0 nn1 Qcell ((9323:ℚ)/12800) ((9361:ℚ)/12800) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((9361:ℚ)/12800) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound source26 nn0 nn1 Qcell ((4633:ℚ)/6400) ((9361:ℚ)/12800) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound source26 nn0 nn1 Qcell ((4557:ℚ)/6400) ((9361:ℚ)/12800) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((9361:ℚ)/12800) :=
  cell_join node0_10 node10_20
private theorem node20_22 :
    CellBound source26 nn0 nn1 Qcell ((9361:ℚ)/12800) ((9399:ℚ)/12800) :=
  cell_join leaf20 leaf21
private theorem node23_25 :
    CellBound source26 nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_join leaf23 leaf24
private theorem node22_25 :
    CellBound source26 nn0 nn1 Qcell ((9399:ℚ)/12800) ((591:ℚ)/800) :=
  cell_join leaf22 node23_25
private theorem node20_25 :
    CellBound source26 nn0 nn1 Qcell ((9361:ℚ)/12800) ((591:ℚ)/800) :=
  cell_join node20_22 node22_25
private theorem node25_27 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_join leaf25 leaf26
private theorem node28_30 :
    CellBound source26 nn0 nn1 Qcell ((957:ℚ)/1280) ((4823:ℚ)/6400) :=
  cell_join leaf28 leaf29
private theorem node27_30 :
    CellBound source26 nn0 nn1 Qcell ((2383:ℚ)/3200) ((4823:ℚ)/6400) :=
  cell_join leaf27 node28_30
private theorem node25_30 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((4823:ℚ)/6400) :=
  cell_join node25_27 node27_30
private theorem node20_30 :
    CellBound source26 nn0 nn1 Qcell ((9361:ℚ)/12800) ((4823:ℚ)/6400) :=
  cell_join node20_25 node25_30
private theorem node30_32 :
    CellBound source26 nn0 nn1 Qcell ((4823:ℚ)/6400) ((61:ℚ)/80) :=
  cell_join leaf30 leaf31
private theorem node33_35 :
    CellBound source26 nn0 nn1 Qcell ((2459:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join leaf33 leaf34
private theorem node32_35 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf32 node33_35
private theorem node30_35 :
    CellBound source26 nn0 nn1 Qcell ((4823:ℚ)/6400) ((629:ℚ)/800) :=
  cell_join node30_32 node32_35
private theorem node35_37 :
    CellBound source26 nn0 nn1 Qcell ((629:ℚ)/800) ((343:ℚ)/400) :=
  cell_join leaf35 leaf36
private theorem node38_40 :
    CellBound source26 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf38 leaf39
private theorem node37_40 :
    CellBound source26 nn0 nn1 Qcell ((343:ℚ)/400) ((69:ℚ)/50) :=
  cell_join leaf37 node38_40
private theorem node35_40 :
    CellBound source26 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node35_37 node37_40
private theorem node30_40 :
    CellBound source26 nn0 nn1 Qcell ((4823:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node30_35 node35_40
private theorem node20_40 :
    CellBound source26 nn0 nn1 Qcell ((9361:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node20_30 node30_40
private theorem node0_40 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_20 node20_40
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_40
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29,packet30,packet31,packet32,packet33,packet34,packet35,packet36,packet37,packet38,packet39]
theorem packet_count : packets.length = 40 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC32
#check @N11Formalization.C450Source26GroupedC32.bound
#print axioms N11Formalization.C450Source26GroupedC32.valid0
#print axioms N11Formalization.C450Source26GroupedC32.valid1
#print axioms N11Formalization.C450Source26GroupedC32.valid2
#print axioms N11Formalization.C450Source26GroupedC32.valid3
#print axioms N11Formalization.C450Source26GroupedC32.valid4
#print axioms N11Formalization.C450Source26GroupedC32.valid5
#print axioms N11Formalization.C450Source26GroupedC32.valid6
#print axioms N11Formalization.C450Source26GroupedC32.valid7
#print axioms N11Formalization.C450Source26GroupedC32.valid8
#print axioms N11Formalization.C450Source26GroupedC32.valid9
#print axioms N11Formalization.C450Source26GroupedC32.valid10
#print axioms N11Formalization.C450Source26GroupedC32.valid11
#print axioms N11Formalization.C450Source26GroupedC32.valid12
#print axioms N11Formalization.C450Source26GroupedC32.valid13
#print axioms N11Formalization.C450Source26GroupedC32.valid14
#print axioms N11Formalization.C450Source26GroupedC32.valid15
#print axioms N11Formalization.C450Source26GroupedC32.valid16
#print axioms N11Formalization.C450Source26GroupedC32.valid17
#print axioms N11Formalization.C450Source26GroupedC32.valid18
#print axioms N11Formalization.C450Source26GroupedC32.valid19
#print axioms N11Formalization.C450Source26GroupedC32.valid20
#print axioms N11Formalization.C450Source26GroupedC32.valid21
#print axioms N11Formalization.C450Source26GroupedC32.valid22
#print axioms N11Formalization.C450Source26GroupedC32.valid23
#print axioms N11Formalization.C450Source26GroupedC32.valid24
#print axioms N11Formalization.C450Source26GroupedC32.valid25
#print axioms N11Formalization.C450Source26GroupedC32.valid26
#print axioms N11Formalization.C450Source26GroupedC32.valid27
#print axioms N11Formalization.C450Source26GroupedC32.valid28
#print axioms N11Formalization.C450Source26GroupedC32.valid29
#print axioms N11Formalization.C450Source26GroupedC32.valid30
#print axioms N11Formalization.C450Source26GroupedC32.valid31
#print axioms N11Formalization.C450Source26GroupedC32.valid32
#print axioms N11Formalization.C450Source26GroupedC32.valid33
#print axioms N11Formalization.C450Source26GroupedC32.valid34
#print axioms N11Formalization.C450Source26GroupedC32.valid35
#print axioms N11Formalization.C450Source26GroupedC32.valid36
#print axioms N11Formalization.C450Source26GroupedC32.valid37
#print axioms N11Formalization.C450Source26GroupedC32.valid38
#print axioms N11Formalization.C450Source26GroupedC32.valid39
#print axioms N11Formalization.C450Source26GroupedC32.bound
#print axioms N11Formalization.C450Source26GroupedC32.endpoint_checks
