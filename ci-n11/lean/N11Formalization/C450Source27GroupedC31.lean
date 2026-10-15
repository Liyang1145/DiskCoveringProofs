import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((7:ℚ)/8),((15:ℚ)/16),((1042885697:ℚ)/2000000000),((1386067577:ℚ)/2500000000),((8900199879:ℚ)/10300000000),(1:ℚ),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2036673263:ℚ)/2500000000),((-22385928145131284153783269075236892857:ℚ)/54636350000000000000000000000000000000),((-28383104136620250554849799:ℚ)/73932800000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((5452319131:ℚ)/10000000000),((2891210337:ℚ)/5000000000),((15388744639:ℚ)/17800000000),(1:ℚ),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1926795889:ℚ)/2500000000),((-56383323275148546749860652433002037682532906326537673:ℚ)/137689257812500000000000000000000000000000000000000000),((-692098501434741980096277871:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((1138036383:ℚ)/2000000000),((5901478739:ℚ)/10000000000),((9566254681:ℚ)/10870000000),((21032436217:ℚ)/21360000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((72468519:ℚ)/100000000),((-3440342688353328027988625570156053982778859609434319247:ℚ)/8027284393750000000000000000000000000000000000000000000),((-82027839424297366480260437:ℚ)/221798400000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((232364151:ℚ)/400000000),((6020526179:ℚ)/10000000000),((1946549057:ℚ)/2212000000),((21389578537:ℚ)/21740000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((700754729:ℚ)/1000000000),((-452430655392173805501203007727226673709112709336639:ℚ)/1056952356250000000000000000000000000000000000000000),((-3239244084015045580861733:ℚ)/8871936000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((5928019717:ℚ)/10000000000),((1216009217:ℚ)/2000000000),((49496138019:ℚ)/55775000000),((4313627651:ℚ)/4424000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((169031591:ℚ)/250000000),((-29632412317145019059716191281557385667253574676231504877:ℚ)/67776442816162109375000000000000000000000000000000000000),((-670587086287566433370904879:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((7:ℚ)/8),((15:ℚ)/16),((1496868891:ℚ)/2500000000),((383722721:ℚ)/625000000),((12478082237:ℚ)/14062500000),((1359168163:ℚ)/1394375000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((663525583:ℚ)/1000000000),((-9886630366842845386389635830513754898849934918078777:ℚ)/22631138563156127929687500000000000000000000000000000),((-124918090414175239505815373:ℚ)/346560000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((6046930043:ℚ)/10000000000),((96860603:ℚ)/156250000),((50328510301:ℚ)/56725000000),((342581809:ℚ)/351562500),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((650718627:ℚ)/1000000000),((-1244945358462049276636778136850687670888220681179699803:ℚ)/2851960719970703125000000000000000000000000000000000000),((-661873771411550866534920239:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((1526595797:ℚ)/2500000000),((6228835241:ℚ)/10000000000),((409231309:ℚ)/459375000),((22014505723:ℚ)/22690000000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((3188463993:ℚ)/5000000000),((-89056812914085691456333235734588042150067386429249:ℚ)/201957893371582031250000000000000000000000000000000),((-41234373012149516869573199:ℚ)/115520000000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((6136109271:ℚ)/10000000000),((3129295657:ℚ)/5000000000),((50952764897:ℚ)/57200000000),((11051886971:ℚ)/11392500000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((6310934947:ℚ)/10000000000),((-515573049488267242964045252420252126131996163229140193391:ℚ)/1169682800000000000000000000000000000000000000000000000000),((-1972718914118269137557674853:ℚ)/5544960000000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((7:ℚ)/8),((15:ℚ)/16),((6165835033:ℚ)/10000000000),((3144173409:ℚ)/5000000000),((51160845231:ℚ)/57437500000),((853578479:ℚ)/880000000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((6244341223:ℚ)/10000000000),((-521804036372127096996946074519482493099447651199961271993:ℚ)/1184313291931152343750000000000000000000000000000000000000),((-655396278968084044693865879:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((3097780239:ℚ)/5000000000),((4936017:ℚ)/7812500),((25684461673:ℚ)/28837500000),((69632204:ℚ)/71796875),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((9651761:ℚ)/15625000),((-859516221511760736081114291970641326763101885775557:ℚ)/1951603641986846923828125000000000000000000000000000),((-489914917840796732471586293:ℚ)/1386240000000000000000000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2307:ℚ)/3200),((4633:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((6225285609:ℚ)/10000000000),((6347856147:ℚ)/10000000000),((51576999263:ℚ)/57912500000),((22371568441:ℚ)/23070000000),((1905827251:ℚ)/2000000000),((1907725537:ℚ)/2000000000),((3080928657:ℚ)/10000000000),((6109271573:ℚ)/10000000000),((-21376859007872428720689042345958256595291501275625024209:ℚ)/48557570379394531250000000000000000000000000000000000000),((-102796390311158625430780967:ℚ)/291840000000000000000000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4633:ℚ)/6400),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((48867269:ℚ)/78125000),((1275521997:ℚ)/2000000000),((404570883:ℚ)/454296875),((4492165991:ℚ)/4633000000),((9519843613:ℚ)/10000000000),((476456813:ℚ)/500000000),((622285377:ℚ)/2000000000),((3020376429:ℚ)/5000000000),((-1031510159761867052254581911844286013370030702569189:ℚ)/2344008903205394744873046875000000000000000000000000),((-633660178779178213752261:ℚ)/1805000000000000000000000)⟩
theorem valid12 : Valid source27 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source27 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1163:ℚ)/1600),((4671:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((6284734949:ℚ)/10000000000),((3203681641:ℚ)/5000000000),((51993144643:ℚ)/58387500000),((11275044923:ℚ)/11630000000),((148605427:ℚ)/156250000),((4759921809:ℚ)/5000000000),((98156347:ℚ)/312500000),((1194309543:ℚ)/2000000000),((-14845045912403890477528704293718964045195548727290349:ℚ)/33747157689929008483886718750000000000000000000000000),((-646692543147779292041433711:ℚ)/1848320000000000000000000000)⟩
theorem valid13 : Valid source27 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((4671:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4671:ℚ)/6400),((469:ℚ)/640),((7:ℚ)/8),((15:ℚ)/16),((1578614791:ℚ)/2500000000),((1287423209:ℚ)/2000000000),((13050303537:ℚ)/14656250000),((4527869627:ℚ)/4671000000),((9501845013:ℚ)/10000000000),((9510747333:ℚ)/10000000000),((792422551:ℚ)/2500000000),((2950815821:ℚ)/5000000000),((-8652184892714797237891580936458214362988684041956178479:ℚ)/19676534461975097656250000000000000000000000000000000000),((-2120122911224559480110189:ℚ)/6080000000000000000000000)⟩
theorem valid14 : Valid source27 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source27 nn0 nn1 Qcell ((4671:ℚ)/6400) ((469:ℚ)/640) :=
  cell_of_packet source27 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((6344183081:ℚ)/10000000000),((6466868279:ℚ)/10000000000),((52409281567:ℚ)/58862500000),((22728604837:ℚ)/23450000000),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((1457744677:ℚ)/2500000000),((-32957930417839108434369154950711898874454424611663564153:ℚ)/74980305627441406250000000000000000000000000000000000000),((-642342488287993041841649271:ℚ)/1848320000000000000000000000)⟩
theorem valid15 : Valid source27 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source27 nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((398369169:ℚ)/625000000),((6496619991:ℚ)/10000000000),((3288584183:ℚ)/3693750000),((22817859973:ℚ)/23545000000),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5759561439:ℚ)/10000000000),((-11533263372571000494709812664536453178841152599424283:ℚ)/26248305130004882812500000000000000000000000000000000),((-7501967724021114560644313:ℚ)/21660000000000000000000000)⟩
theorem valid16 : Valid source27 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source27 nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((1600907509:ℚ)/2500000000),((6526371187:ℚ)/10000000000),((13206352563:ℚ)/14834375000),((22907113561:ℚ)/23640000000),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((5687350679:ℚ)/10000000000),((-8961476603198522321159077508140071612490842022190871709:ℚ)/20402706284141540527343750000000000000000000000000000000),((-39874602315359432518958991:ℚ)/115520000000000000000000000)⟩
theorem valid17 : Valid source27 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((6433353081:ℚ)/10000000000),((3278060937:ℚ)/5000000000),((53033471567:ℚ)/59575000000),((11498182811:ℚ)/11867500000),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((5614315447:ℚ)/10000000000),((-580239678477280272398646948850472409626817713783414160009:ℚ)/1321515223339843750000000000000000000000000000000000000000),((-1907458984652814436149767813:ℚ)/5544960000000000000000000000)⟩
theorem valid18 : Valid source27 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source27 nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((3231537921:ℚ)/5000000000),((6615621743:ℚ)/10000000000),((26620765447:ℚ)/30025000000),((23174865229:ℚ)/23830000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2770211387:ℚ)/5000000000),((-18374656522470658509538010498401000320751977632416201401:ℚ)/42293056665039062500000000000000000000000000000000000000),((-473561584187169141210991253:ℚ)/1386240000000000000000000000)⟩
theorem valid19 : Valid source27 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source27 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((260900821:ℚ)/400000000),((6675119647:ℚ)/10000000000),((715435249:ℚ)/807000000),((23353358941:ℚ)/24020000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((5389922141:ℚ)/10000000000),((-118854029641356930030187141654769494073430567150221:ℚ)/273728095312500000000000000000000000000000000000000),((-1003310501566411684833551:ℚ)/2957312000000000000000000)⟩
theorem valid20 : Valid source27 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source27 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((6581964113:ℚ)/10000000000),((673461563:ℚ)/1000000000),((54073748791:ℚ)/61000000000),((2353184689:ℚ)/2421000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((41884301:ℚ)/80000000),((-615626430853689902332741654342330334716732249838162648337:ℚ)/1418631250000000000000000000000000000000000000000000000000),((-622723872372720816727056359:ℚ)/1848320000000000000000000000)⟩
theorem valid21 : Valid source27 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source27 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source27 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((6641406631:ℚ)/10000000000),((1370720403:ℚ)/2000000000),((18163282139:ℚ)/20650000000),((4777761209:ℚ)/4880000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((5076911809:ℚ)/10000000000),((-23405002361488798899126744307518949326232736842999191037:ℚ)/55035153906250000000000000000000000000000000000000000000),((-613919320756213491182702871:ℚ)/1848320000000000000000000000)⟩
theorem valid22 : Valid source27 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((1352057711:ℚ)/2000000000),((3486290619:ℚ)/5000000000),((11064403977:ℚ)/12580000000),((12122871857:ℚ)/12390000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((4745210719:ℚ)/10000000000),((-1322028040079116425476145106763827659188386162172977599:ℚ)/3110727362500000000000000000000000000000000000000000000),((-24209405149436797551721831:ℚ)/73932800000000000000000000)⟩
theorem valid23 : Valid source27 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source27 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((6879166487:ℚ)/10000000000),((3605259733:ℚ)/5000000000),((56154165409:ℚ)/64800000000),((12479779199:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((17562227:ℚ)/40000000),((-25769478644433594302011902284930999232632508910385013029:ℚ)/62985600000000000000000000000000000000000000000000000000),((-587635943949014333201984759:ℚ)/1848320000000000000000000000)⟩
theorem valid24 : Valid source27 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source27 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((3558455541:ℚ)/5000000000),((816204183:ℚ)/1000000000),((28909188787:ℚ)/36200000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((3584672609:ℚ)/10000000000),((-6153573035144300441797190560453615963699034148440290981:ℚ)/18530440625000000000000000000000000000000000000000000000),((-419195878555330565302737773:ℚ)/1386240000000000000000000000)⟩
theorem valid25 : Valid source27 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((4033880457:ℚ)/5000000000),((4556637189:ℚ)/5000000000),((32237163199:ℚ)/40000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-34025164283466627659844639485982875714261732105435108553:ℚ)/100000000000000000000000000000000000000000000000000000000),((-38780001:ℚ)/128000000)⟩
theorem valid26 : Valid source27 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source27 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((4509224551:ℚ)/5000000000),((645825277:ℚ)/500000000),((35564571857:ℚ)/55200000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-2427964467977215161848006362650632071:ℚ)/14016384000000000000000000000000000000),((-38780001:ℚ)/128000000)⟩
theorem valid27 : Valid source27 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet27 valid27
private theorem node1_3 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source27 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2269:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source27 nn0 nn1 Qcell ((4557:ℚ)/6400) ((919:ℚ)/1280) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source27 nn0 nn1 Qcell ((2269:ℚ)/3200) ((919:ℚ)/1280) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source27 nn0 nn1 Qcell ((919:ℚ)/1280) ((4633:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source27 nn0 nn1 Qcell ((4633:ℚ)/6400) ((4671:ℚ)/6400) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source27 nn0 nn1 Qcell ((919:ℚ)/1280) ((4671:ℚ)/6400) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source27 nn0 nn1 Qcell ((2269:ℚ)/3200) ((4671:ℚ)/6400) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((4671:ℚ)/6400) :=
  cell_join node0_7 node7_14
private theorem node15_17 :
    CellBound source27 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source27 nn0 nn1 Qcell ((4671:ℚ)/6400) ((591:ℚ)/800) :=
  cell_join leaf14 node15_17
private theorem node17_19 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_join leaf17 leaf18
private theorem node19_21 :
    CellBound source27 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf19 leaf20
private theorem node17_21 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((2421:ℚ)/3200) :=
  cell_join node17_19 node19_21
private theorem node14_21 :
    CellBound source27 nn0 nn1 Qcell ((4671:ℚ)/6400) ((2421:ℚ)/3200) :=
  cell_join node14_17 node17_21
private theorem node22_24 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf22 leaf23
private theorem node21_24 :
    CellBound source27 nn0 nn1 Qcell ((2421:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join leaf21 node22_24
private theorem node24_26 :
    CellBound source27 nn0 nn1 Qcell ((629:ℚ)/800) ((181:ℚ)/200) :=
  cell_join leaf24 leaf25
private theorem node26_28 :
    CellBound source27 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf26 leaf27
private theorem node24_28 :
    CellBound source27 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node24_26 node26_28
private theorem node21_28 :
    CellBound source27 nn0 nn1 Qcell ((2421:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node21_24 node24_28
private theorem node14_28 :
    CellBound source27 nn0 nn1 Qcell ((4671:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node14_21 node21_28
private theorem node0_28 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_14 node14_28
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_28
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27]
theorem packet_count : packets.length = 28 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC31
#check @N11Formalization.C450Source27GroupedC31.bound
#print axioms N11Formalization.C450Source27GroupedC31.valid0
#print axioms N11Formalization.C450Source27GroupedC31.valid1
#print axioms N11Formalization.C450Source27GroupedC31.valid2
#print axioms N11Formalization.C450Source27GroupedC31.valid3
#print axioms N11Formalization.C450Source27GroupedC31.valid4
#print axioms N11Formalization.C450Source27GroupedC31.valid5
#print axioms N11Formalization.C450Source27GroupedC31.valid6
#print axioms N11Formalization.C450Source27GroupedC31.valid7
#print axioms N11Formalization.C450Source27GroupedC31.valid8
#print axioms N11Formalization.C450Source27GroupedC31.valid9
#print axioms N11Formalization.C450Source27GroupedC31.valid10
#print axioms N11Formalization.C450Source27GroupedC31.valid11
#print axioms N11Formalization.C450Source27GroupedC31.valid12
#print axioms N11Formalization.C450Source27GroupedC31.valid13
#print axioms N11Formalization.C450Source27GroupedC31.valid14
#print axioms N11Formalization.C450Source27GroupedC31.valid15
#print axioms N11Formalization.C450Source27GroupedC31.valid16
#print axioms N11Formalization.C450Source27GroupedC31.valid17
#print axioms N11Formalization.C450Source27GroupedC31.valid18
#print axioms N11Formalization.C450Source27GroupedC31.valid19
#print axioms N11Formalization.C450Source27GroupedC31.valid20
#print axioms N11Formalization.C450Source27GroupedC31.valid21
#print axioms N11Formalization.C450Source27GroupedC31.valid22
#print axioms N11Formalization.C450Source27GroupedC31.valid23
#print axioms N11Formalization.C450Source27GroupedC31.valid24
#print axioms N11Formalization.C450Source27GroupedC31.valid25
#print axioms N11Formalization.C450Source27GroupedC31.valid26
#print axioms N11Formalization.C450Source27GroupedC31.valid27
#print axioms N11Formalization.C450Source27GroupedC31.bound
#print axioms N11Formalization.C450Source27GroupedC31.endpoint_checks
