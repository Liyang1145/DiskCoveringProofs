import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((668485881:ℚ)/1000000000),((6878750003:ℚ)/10000000000),(-1:ℚ),((-1826257643:ℚ)/2022000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4958036103:ℚ)/10000000000),((417393562686784251475427757678629:ℚ)/6814140000000000000000000000000000),((7713756013681954917506867:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((6803658467:ℚ)/10000000000),((6997500003:ℚ)/10000000000),(-1:ℚ),((-18618975401:ℚ)/20600000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((2309378377:ℚ)/5000000000),((129536495765257052206310827091859619:ℚ)/2121800000000000000000000000000000000),((7744038816784061055006867:ℚ)/14440000000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((6922456291:ℚ)/10000000000),((3528437501:ℚ)/5000000000),(-1:ℚ),((-18975368873:ℚ)/20790000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((4254586847:ℚ)/10000000000),((1020346780287516820098937796236127:ℚ)/17151750000000000000000000000000000),((1939797071924765114375763:ℚ)/3610000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((6981854547:ℚ)/10000000000),((7086562503:ℚ)/10000000000),(-1:ℚ),((-19153563641:ℚ)/20885000000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((406108477:ℚ)/1000000000),((64034873113145221202551720058181999:ℚ)/1090458062500000000000000000000000000),((7766765040944136751881867:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((1752888379:ℚ)/2500000000),((7116250003:ℚ)/10000000000),(-1:ℚ),((-4810665137:ℚ)/5245000000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3960997047:ℚ)/10000000000),((4036544030799017912668872414074187:ℚ)/68775062500000000000000000000000000),((7774343138870542192506867:ℚ)/14440000000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),(-1:ℚ),((-15:ℚ)/16),((3520626191:ℚ)/5000000000),((3572968751:ℚ)/5000000000),(-1:ℚ),((-9665878573:ℚ)/10537500000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((1929227363:ℚ)/5000000000),((1628429594460025081323536663037373:ℚ)/27759726562500000000000000000000000),((1945480645369535217500763:ℚ)/3610000000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((843:ℚ)/1280),((8449:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((883868893:ℚ)/1250000000),((1790195313:ℚ)/2500000000),(-1:ℚ),((-2427606679:ℚ)/2640312500),((4890720817:ℚ)/5000000000),((1957725423:ℚ)/2000000000),((83782417:ℚ)/400000000),((1876628081:ℚ)/5000000000),((65013767176255227207872918580572847:ℚ)/1115400015625000000000000000000000000),((486607050453798684160347:ℚ)/902500000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((843:ℚ)/1280) ((8449:ℚ)/12800) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((8449:ℚ)/12800),((2117:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((885725061:ℚ)/1250000000),((7175625003:ℚ)/10000000000),(-1:ℚ),((-2433175183:ℚ)/2646250000),((9774321709:ℚ)/10000000000),((9781441639:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1849795023:ℚ)/5000000000),((4080703564707320406802005668370793:ℚ)/70026390625000000000000000000000000),((7789503369532923386256867:ℚ)/14440000000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((8449:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2117:ℚ)/3200),((8487:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((3550324903:ℚ)/5000000000),((7190468753:ℚ)/10000000000),(-1:ℚ),((-9754974709:ℚ)/10608750000),((9767266893:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((2161672951:ℚ)/10000000000),((3645170889:ℚ)/10000000000),((3642744827873013012897205490621683:ℚ)/62525320312500000000000000000000000),((7793294267783845833131867:ℚ)/14440000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((2117:ℚ)/3200) ((8487:ℚ)/12800) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8487:ℚ)/12800),((4253:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7115499099:ℚ)/10000000000),((7205312503:ℚ)/10000000000),(-1:ℚ),((-19554497297:ℚ)/21265000000),((9760276751:ℚ)/10000000000),((4883633449:ℚ)/5000000000),((438804929:ℚ)/2000000000),((179498219:ℚ)/500000000),((131696433167570129128718578851630231:ℚ)/2261001125000000000000000000000000000),((7797085502268899139381867:ℚ)/14440000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((8487:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4253:ℚ)/6400),((341:ℚ)/512),(-1:ℚ),((-15:ℚ)/16),((445646773:ℚ)/625000000),((7220156253:ℚ)/10000000000),(-1:ℚ),((-1224940319:ℚ)/1332031250),((195067017:ℚ)/200000000),((2440069189:ℚ)/2500000000),((1112811311:ℚ)/5000000000),((706786711:ℚ)/2000000000),((165319214778319096926098571157103:ℚ)/2838891601562500000000000000000000),((7800877072988083305006867:ℚ)/14440000000000000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((4253:ℚ)/6400) ((341:ℚ)/512) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((341:ℚ)/512),((17069:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((1786299403:ℚ)/2500000000),((7227578127:ℚ)/10000000000),(-1:ℚ),((-4910898209:ℚ)/5334062500),((609369491:ℚ)/625000000),((1950670171:ℚ)/2000000000),((4482299:ℚ)/20000000),((695407701:ℚ)/2000000000),((264264921637562223613761270402841743:ℚ)/4552355640625000000000000000000000000),((7802772984180019675862427:ℚ)/14440000000000000000000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((341:ℚ)/512) ((17069:ℚ)/25600) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((17069:ℚ)/25600),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((286104889:ℚ)/400000000),((3617500001:ℚ)/5000000000),(-1:ℚ),((-786634667:ℚ)/854400000),((4873244381:ℚ)/5000000000),((9749911861:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((862063383:ℚ)/2500000000),((21186007929103504662616647077801:ℚ)/364999680000000000000000000000000),((1951167244921483055000763:ℚ)/3610000000000000000000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((17069:ℚ)/25600) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((267:ℚ)/400),((17107:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((7160046831:ℚ)/10000000000),((7242421877:ℚ)/10000000000),(-1:ℚ),((-19688140493:ℚ)/21383750000),((4871540757:ℚ)/5000000000),((9746488767:ℚ)/10000000000),((283959837:ℚ)/1250000000),((3419236027:ℚ)/10000000000),((265385935386981185262560388184741523:ℚ)/4572647640625000000000000000000000000),((7806565059250377478987427:ℚ)/14440000000000000000000000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((17107:ℚ)/25600) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((17107:ℚ)/25600),((8563:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((895933929:ℚ)/1250000000),((906230469:ℚ)/1250000000),(-1:ℚ),((-2463801787:ℚ)/2675937500),((9739690061:ℚ)/10000000000),((9743081519:ℚ)/10000000000),((1143344217:ℚ)/5000000000),((3389980001:ℚ)/10000000000),((66486857535058542883344432627799167:ℚ)/1145702640625000000000000000000000000),((122007206607396178950243:ℚ)/225625000000000000000000)⟩
theorem valid14 : Valid source15 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source15 nn0 nn1 Qcell ((17107:ℚ)/25600) ((8563:ℚ)/12800) :=
  cell_of_packet source15 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((8563:ℚ)/12800),((3429:ℚ)/5120),(-1:ℚ),((-15:ℚ)/16),((7174896027:ℚ)/10000000000),((7257265627:ℚ)/10000000000),(-1:ℚ),((-19732688081:ℚ)/21431250000),((194726287:ℚ)/200000000),((4869845033:ℚ)/5000000000),((460306597:ℚ)/2000000000),((1680239611:ℚ)/5000000000),((1332547917194553427337689968066619:ℚ)/22964923828125000000000000000000000),((7810357470554866141487427:ℚ)/14440000000000000000000000)⟩
theorem valid15 : Valid source15 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source15 nn0 nn1 Qcell ((8563:ℚ)/12800) ((3429:ℚ)/5120) :=
  cell_of_packet source15 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((3429:ℚ)/5120),((4291:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((1436464123:ℚ)/2000000000),((3632343751:ℚ)/5000000000),(-1:ℚ),((-3950992369:ℚ)/4291000000),((1216619291:ℚ)/1250000000),((1947262871:ℚ)/2000000000),((1158107867:ℚ)/5000000000),((1665363591:ℚ)/5000000000),((333840494139914939946395192128217:ℚ)/5753962812500000000000000000000000),((1953063450573727386250763:ℚ)/3610000000000000000000000)⟩
theorem valid16 : Valid source15 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source15 nn0 nn1 Qcell ((3429:ℚ)/5120) ((4291:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((4291:ℚ)/6400),((17183:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((3594872599:ℚ)/5000000000),((3636054689:ℚ)/5000000000),(-1:ℚ),((-9888617797:ℚ)/10739375000),((9729609943:ℚ)/10000000000),((9732954333:ℚ)/10000000000),((2330739941:ℚ)/10000000000),((3300717071:ℚ)/10000000000),((267635865471978467702962897592494039:ℚ)/4613367015625000000000000000000000000),((1953537554587252100568123:ℚ)/3610000000000000000000000)⟩
theorem valid17 : Valid source15 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source15 nn0 nn1 Qcell ((4291:ℚ)/6400) ((17183:ℚ)/25600) :=
  cell_of_packet source15 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((17183:ℚ)/25600),((8601:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((3598584887:ℚ)/5000000000),((1819882813:ℚ)/2500000000),(-1:ℚ),((-9899754661:ℚ)/10751250000),((1215785143:ℚ)/1250000000),((2432402487:ℚ)/2500000000),((2345108749:ℚ)/10000000000),((3270441783:ℚ)/10000000000),((44581116030181349782330860840233:ℚ)/768546386718750000000000000000000),((488502919871912156035347:ℚ)/902500000000000000000000)⟩
theorem valid18 : Valid source15 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source15 nn0 nn1 Qcell ((17183:ℚ)/25600) ((8601:ℚ)/12800) :=
  cell_of_packet source15 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((8601:ℚ)/12800),((17221:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((1440918869:ℚ)/2000000000),((910869141:ℚ)/1250000000),(-1:ℚ),((-3964356607:ℚ)/4305250000),((9722967879:ℚ)/10000000000),((9726281149:ℚ)/10000000000),((2359325197:ℚ)/10000000000),((3239893869:ℚ)/10000000000),((632387719426494163954838989680109:ℚ)/10903045625000000000000000000000000),((122155364095652834923203:ℚ)/225625000000000000000000)⟩
theorem valid19 : Valid source15 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source15 nn0 nn1 Qcell ((8601:ℚ)/12800) ((17221:ℚ)/25600) :=
  cell_of_packet source15 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((17221:ℚ)/25600),((431:ℚ)/640),(-1:ℚ),((-15:ℚ)/16),((7212018909:ℚ)/10000000000),((7294375003:ℚ)/10000000000),(-1:ℚ),((-19844056727:ℚ)/21550000000),((607479381:ℚ)/625000000),((2430741971:ℚ)/2500000000),((2373392223:ℚ)/10000000000),((401133193:ℚ)/1250000000),((8416569554991985430205560903904541:ℚ)/145125781250000000000000000000000000),((7819839970095967023756867:ℚ)/14440000000000000000000000)⟩
theorem valid20 : Valid source15 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source15 nn0 nn1 Qcell ((17221:ℚ)/25600) ((431:ℚ)/640) :=
  cell_of_packet source15 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((431:ℚ)/640),((8639:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((1804860867:ℚ)/2500000000),((7309218753:ℚ)/10000000000),(-1:ℚ),((-4966582601:ℚ)/5399375000),((4856560387:ℚ)/5000000000),((9719670101:ℚ)/10000000000),((9604357:ℚ)/40000000),((3177948629:ℚ)/10000000000),((416063473907628167395833631700181:ℚ)/7154171875000000000000000000000000),((7823633558219936345631867:ℚ)/14440000000000000000000000)⟩
theorem valid21 : Valid source15 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source15 nn0 nn1 Qcell ((431:ℚ)/640) ((8639:ℚ)/12800) :=
  cell_of_packet source15 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((8639:ℚ)/12800),((4329:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((904286571:ℚ)/1250000000),((3662031251:ℚ)/5000000000),(-1:ℚ),((-2488859713:ℚ)/2705625000),((2426658193:ℚ)/2500000000),((9713120779:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((1557407167:ℚ)/5000000000),((17025607235288135030490309452305471:ℚ)/292816265625000000000000000000000000),((1956856870580608626875763:ℚ)/3610000000000000000000000)⟩
theorem valid22 : Valid source15 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source15 nn0 nn1 Qcell ((8639:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((4329:ℚ)/6400),((8677:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((1812285411:ℚ)/2500000000),((1834726563:ℚ)/2500000000),(-1:ℚ),((-4988856233:ℚ)/5423125000),((9700205687:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((306851119:ℚ)/1250000000),((3050417091:ℚ)/10000000000),((68387170109931384124640409533086071:ℚ)/1176411390625000000000000000000000000),((489451358932165181035347:ℚ)/902500000000000000000000)⟩
theorem valid23 : Valid source15 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source15 nn0 nn1 Qcell ((4329:ℚ)/6400) ((8677:ℚ)/12800) :=
  cell_of_packet source15 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((8677:ℚ)/12800),((1087:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((7263990697:ℚ)/10000000000),((3676875001:ℚ)/5000000000),(-1:ℚ),((-19999972091:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((2425051423:ℚ)/2500000000),((2480870833:ℚ)/10000000000),((1492337539:ℚ)/5000000000),((137345139180611795208126911407863551:ℚ)/2363138000000000000000000000000000000),((1958754084935245536250763:ℚ)/3610000000000000000000000)⟩
theorem valid24 : Valid source15 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source15 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1087:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((3639419863:ℚ)/5000000000),((7383437503:ℚ)/10000000000),(-1:ℚ),((-10022259589:ℚ)/10917500000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((72937433:ℚ)/250000000),((8706523498377726075046844968536921:ℚ)/148989757812500000000000000000000000),((7842606542351745845631867:ℚ)/14440000000000000000000000)⟩
theorem valid25 : Valid source15 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7308537717:ℚ)/10000000000),((3706562501:ℚ)/5000000000),(-1:ℚ),((-20133613151:ℚ)/21930000000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((2778415479:ℚ)/10000000000),((70228441291747958294626681647908111:ℚ)/1202312250000000000000000000000000000),((1962549522346911933125763:ℚ)/3610000000000000000000000)⟩
theorem valid26 : Valid source15 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source15 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),(-1:ℚ),((-15:ℚ)/16),((229319863:ℚ)/312500000),((7472500003:ℚ)/10000000000),(-1:ℚ),((-631959589:ℚ)/691250000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2632194327:ℚ)/10000000000),((40293555777487105756561294068521:ℚ)/682609375000000000000000000000000),((7865385219036235605006867:ℚ)/14440000000000000000000000)⟩
theorem valid27 : Valid source15 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7397631147:ℚ)/10000000000),((3765937501:ℚ)/5000000000),(-1:ℚ),((-886995367:ℚ)/970000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((231285527:ℚ)/1000000000),((69357709988398492606392575067393:ℚ)/1176125000000000000000000000000000),((1970144431979815039375763:ℚ)/3610000000000000000000000)⟩
theorem valid28 : Valid source15 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),(-1:ℚ),((-15:ℚ)/16),((932128291:ℚ)/1250000000),((7591250003:ℚ)/10000000000),(-1:ℚ),((-2572384873:ℚ)/2812500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1942761279:ℚ)/10000000000),((388361607887970106242046398602509:ℚ)/6591796875000000000000000000000000),((7895775617060216742506867:ℚ)/14440000000000000000000000)⟩
theorem valid29 : Valid source15 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source15 nn0 nn1 packet29 valid29
def packet30 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((7516421167:ℚ)/10000000000),((7710000003:ℚ)/10000000000),(-1:ℚ),((-1596712577:ℚ)/1760000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1484414409:ℚ)/10000000000),((930450840761534319964025934469541:ℚ)/15488000000000000000000000000000000),((273477:ℚ)/500000)⟩
theorem valid30 : Valid source15 packet30 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf30 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet30 valid30
def packet31 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((3817604929:ℚ)/5000000000),((8660000003:ℚ)/10000000000),(-1:ℚ),((-10556814787:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((61751431119474610357826080544033159:ℚ)/839808000000000000000000000000000000),((273477:ℚ)/500000)⟩
theorem valid31 : Valid source15 packet31 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf31 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet31 valid31
def packet32 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((4292739263:ℚ)/5000000000),((5280000001:ℚ)/5000000000),(-1:ℚ),((-11982217789:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((103753821456911550729862914870953629:ℚ)/1280000000000000000000000000000000000),((273477:ℚ)/500000)⟩
theorem valid32 : Valid source15 packet32 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf32 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet32 valid32
def packet33 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((2621465669:ℚ)/2500000000),((14360000003:ℚ)/10000000000),(-1:ℚ),((-7416397007:ℚ)/11040000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((5657521587447967816086041:ℚ)/60940800000000000000000000),((273477:ℚ)/500000)⟩
theorem valid33 : Valid source15 packet33 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf33 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet33 valid33
private theorem node0_2 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source15 nn0 nn1 Qcell ((103:ℚ)/160) ((4177:ℚ)/6400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((4177:ℚ)/6400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source15 nn0 nn1 Qcell ((4177:ℚ)/6400) ((843:ℚ)/1280) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source15 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source15 nn0 nn1 Qcell ((4177:ℚ)/6400) ((2117:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source15 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source15 nn0 nn1 Qcell ((4253:ℚ)/6400) ((17069:ℚ)/25600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source15 nn0 nn1 Qcell ((2117:ℚ)/3200) ((17069:ℚ)/25600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source15 nn0 nn1 Qcell ((17069:ℚ)/25600) ((17107:ℚ)/25600) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source15 nn0 nn1 Qcell ((8563:ℚ)/12800) ((4291:ℚ)/6400) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source15 nn0 nn1 Qcell ((17107:ℚ)/25600) ((4291:ℚ)/6400) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source15 nn0 nn1 Qcell ((17069:ℚ)/25600) ((4291:ℚ)/6400) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source15 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4291:ℚ)/6400) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((4291:ℚ)/6400) :=
  cell_join node0_8 node8_17
private theorem node17_19 :
    CellBound source15 nn0 nn1 Qcell ((4291:ℚ)/6400) ((8601:ℚ)/12800) :=
  cell_join leaf17 leaf18
private theorem node19_21 :
    CellBound source15 nn0 nn1 Qcell ((8601:ℚ)/12800) ((431:ℚ)/640) :=
  cell_join leaf19 leaf20
private theorem node17_21 :
    CellBound source15 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_join node17_19 node19_21
private theorem node21_23 :
    CellBound source15 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_join leaf21 leaf22
private theorem node23_25 :
    CellBound source15 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join leaf23 leaf24
private theorem node21_25 :
    CellBound source15 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_join node21_23 node23_25
private theorem node17_25 :
    CellBound source15 nn0 nn1 Qcell ((4291:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join node17_21 node21_25
private theorem node25_27 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_join leaf25 leaf26
private theorem node27_29 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf27 leaf28
private theorem node25_29 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join node25_27 node27_29
private theorem node29_31 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf29 leaf30
private theorem node32_34 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf32 leaf33
private theorem node31_34 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf31 node32_34
private theorem node29_34 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node29_31 node31_34
private theorem node25_34 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node25_29 node29_34
private theorem node17_34 :
    CellBound source15 nn0 nn1 Qcell ((4291:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node17_25 node25_34
private theorem node0_34 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_17 node17_34
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_34
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29,packet30,packet31,packet32,packet33]
theorem packet_count : packets.length = 34 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC01
#check @N11Formalization.C450Source15GroupedC01.bound
#print axioms N11Formalization.C450Source15GroupedC01.valid0
#print axioms N11Formalization.C450Source15GroupedC01.valid1
#print axioms N11Formalization.C450Source15GroupedC01.valid2
#print axioms N11Formalization.C450Source15GroupedC01.valid3
#print axioms N11Formalization.C450Source15GroupedC01.valid4
#print axioms N11Formalization.C450Source15GroupedC01.valid5
#print axioms N11Formalization.C450Source15GroupedC01.valid6
#print axioms N11Formalization.C450Source15GroupedC01.valid7
#print axioms N11Formalization.C450Source15GroupedC01.valid8
#print axioms N11Formalization.C450Source15GroupedC01.valid9
#print axioms N11Formalization.C450Source15GroupedC01.valid10
#print axioms N11Formalization.C450Source15GroupedC01.valid11
#print axioms N11Formalization.C450Source15GroupedC01.valid12
#print axioms N11Formalization.C450Source15GroupedC01.valid13
#print axioms N11Formalization.C450Source15GroupedC01.valid14
#print axioms N11Formalization.C450Source15GroupedC01.valid15
#print axioms N11Formalization.C450Source15GroupedC01.valid16
#print axioms N11Formalization.C450Source15GroupedC01.valid17
#print axioms N11Formalization.C450Source15GroupedC01.valid18
#print axioms N11Formalization.C450Source15GroupedC01.valid19
#print axioms N11Formalization.C450Source15GroupedC01.valid20
#print axioms N11Formalization.C450Source15GroupedC01.valid21
#print axioms N11Formalization.C450Source15GroupedC01.valid22
#print axioms N11Formalization.C450Source15GroupedC01.valid23
#print axioms N11Formalization.C450Source15GroupedC01.valid24
#print axioms N11Formalization.C450Source15GroupedC01.valid25
#print axioms N11Formalization.C450Source15GroupedC01.valid26
#print axioms N11Formalization.C450Source15GroupedC01.valid27
#print axioms N11Formalization.C450Source15GroupedC01.valid28
#print axioms N11Formalization.C450Source15GroupedC01.valid29
#print axioms N11Formalization.C450Source15GroupedC01.valid30
#print axioms N11Formalization.C450Source15GroupedC01.valid31
#print axioms N11Formalization.C450Source15GroupedC01.valid32
#print axioms N11Formalization.C450Source15GroupedC01.valid33
#print axioms N11Formalization.C450Source15GroupedC01.bound
#print axioms N11Formalization.C450Source15GroupedC01.endpoint_checks
