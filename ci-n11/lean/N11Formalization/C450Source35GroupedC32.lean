import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((15:ℚ)/16),(1:ℚ),((2419999999:ℚ)/5000000000),((2591795613:ℚ)/5000000000),((9371999997:ℚ)/10300000000),(1:ℚ),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((8804008987:ℚ)/10000000000),((-2087336061561:ℚ)/6437500000000),((-1425292916810393223172281:ℚ)/2432000000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((2538749999:ℚ)/5000000000),((677709559:ℚ)/1250000000),((3242749999:ℚ)/3560000000),(1:ℚ),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((167830921:ℚ)/200000000),((-2857555515466761887360161:ℚ)/8691406250000000000000000),((-1410033857706726985672281:ℚ)/2432000000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((2657499999:ℚ)/5000000000),((346293981:ℚ)/625000000),((10084499997:ℚ)/10870000000),(1:ℚ),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7963196523:ℚ)/10000000000),((-9258008994595626773863562487:ℚ)/27175000000000000000000000000),((-74055120386840513061699:ℚ)/128000000000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((5433749997:ℚ)/10000000000),((5659721363:ℚ)/10000000000),((20525249991:ℚ)/22120000000),(1:ℚ),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((7742192713:ℚ)/10000000000),((-295770125668870305104993097:ℚ)/864062500000000000000000000),((-106382920182130016754960051:ℚ)/184832000000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2776249999:ℚ)/5000000000),((2859613383:ℚ)/5000000000),((10440749997:ℚ)/11155000000),(1:ℚ),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((7516076243:ℚ)/10000000000),((-19396247769142428189402849639:ℚ)/55775000000000000000000000000),((-1398536384608825510672281:ℚ)/2432000000000000000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((15:ℚ)/16),(1:ℚ),((5611874997:ℚ)/10000000000),((144468249:ℚ)/250000000),((7019874997:ℚ)/7500000000),(1:ℚ),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3700474209:ℚ)/5000000000),((-26132381780983732533851083:ℚ)/75000000000000000000000000),((-106019216507309136073710051:ℚ)/184832000000000000000000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((2835624999:ℚ)/5000000000),((1161696149:ℚ)/2000000000),((10618874997:ℚ)/11297500000),(1:ℚ),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((7284350533:ℚ)/10000000000),((-39659682799868370318200429031:ℚ)/112975000000000000000000000000),((-1394433837951682266922281:ℚ)/2432000000000000000000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2850468749:ℚ)/5000000000),((5838230999:ℚ)/10000000000),((10663406247:ℚ)/11345000000),(1:ℚ),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((7225477331:ℚ)/10000000000),((-4982624388154133684498194821:ℚ)/14181250000000000000000000000),((-1392682813743575963797281:ℚ)/2432000000000000000000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((2865312499:ℚ)/5000000000),((5867980729:ℚ)/10000000000),((3569312499:ℚ)/3797500000),(1:ℚ),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((7166208309:ℚ)/10000000000),((-534158178773978417187854511:ℚ)/1519000000000000000000000000),((-73207272705960834936699:ℚ)/128000000000000000000000)⟩
theorem valid8 : Valid source35 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source35 nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet source35 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((2880156249:ℚ)/5000000000),((5897729939:ℚ)/10000000000),((10752468747:ℚ)/11440000000),(1:ℚ),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((7106533251:ℚ)/10000000000),((-314549135750423254673721447:ℚ)/893750000000000000000000000),((-1389199940562033966922281:ℚ)/2432000000000000000000000)⟩
theorem valid9 : Valid source35 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source35 nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((15:ℚ)/16),(1:ℚ),((2894999999:ℚ)/5000000000),((2963739319:ℚ)/5000000000),((10796999997:ℚ)/11487500000),(1:ℚ),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((1761610381:ℚ)/2500000000),((-2023113731675868871046894079:ℚ)/5743750000000000000000000000),((-1387468090292862273172281:ℚ)/2432000000000000000000000)⟩
theorem valid10 : Valid source35 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet source35 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((919:ℚ)/1280),((9209:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((2909843749:ℚ)/5000000000),((5942352797:ℚ)/10000000000),((10841531247:ℚ)/11511250000),(1:ℚ),((74558193:ℚ)/78125000),((4774160179:ℚ)/5000000000),((1516687521:ℚ)/5000000000),((349296103:ℚ)/500000000),((-20344944775769300732656151721:ℚ)/57556250000000000000000000000),((-1387225154824228782547281:ℚ)/2432000000000000000000000)⟩
theorem valid11 : Valid source35 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source35 nn0 nn1 Qcell ((919:ℚ)/1280) ((9209:ℚ)/12800) :=
  cell_of_packet source35 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((9209:ℚ)/12800),((2307:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((364658203:ℚ)/625000000),((5957226831:ℚ)/10000000000),((452658203:ℚ)/480625000),(1:ℚ),((59616423:ℚ)/62500000),((9543448709:ℚ)/10000000000),((762368323:ℚ)/2500000000),((6955498343:ℚ)/10000000000),((-6798244200276062273568848801:ℚ)/19225000000000000000000000000),((-21661950130150154115729:ℚ)/38000000000000000000000)⟩
theorem valid12 : Valid source35 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source35 nn0 nn1 Qcell ((9209:ℚ)/12800) ((2307:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2307:ℚ)/3200),((9247:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((2924687499:ℚ)/5000000000),((298605037:ℚ)/500000000),((10886062497:ℚ)/11558750000),(1:ℚ),((4766928483:ℚ)/5000000000),((1907725537:ℚ)/2000000000),((3065322907:ℚ)/10000000000),((6924963329:ℚ)/10000000000),((-3271114560037562385579278487:ℚ)/9247000000000000000000000000),((-1385506059206405495047281:ℚ)/2432000000000000000000000)⟩
theorem valid13 : Valid source35 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source35 nn0 nn1 Qcell ((2307:ℚ)/3200) ((9247:ℚ)/12800) :=
  cell_of_packet source35 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((9247:ℚ)/12800),((4633:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((1466054687:ℚ)/2500000000),((239478981:ℚ)/400000000),((5454164061:ℚ)/5791250000),(1:ℚ),((1905827251:ℚ)/2000000000),((9533856971:ℚ)/10000000000),((3080928657:ℚ)/10000000000),((6894315501:ℚ)/10000000000),((-40988290141867267490794324377:ℚ)/115825000000000000000000000000),((-346162226838735919367289:ℚ)/608000000000000000000000)⟩
theorem valid14 : Valid source35 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source35 nn0 nn1 Qcell ((9247:ℚ)/12800) ((4633:ℚ)/6400) :=
  cell_of_packet source35 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4633:ℚ)/6400),((1857:ℚ)/2560),((15:ℚ)/16),(1:ℚ),((2939531249:ℚ)/5000000000),((6001848187:ℚ)/10000000000),((3643531249:ℚ)/3868750000),(1:ℚ),((9524465239:ℚ)/10000000000),((476456813:ℚ)/500000000),((3096295161:ℚ)/10000000000),((1715888327:ℚ)/2500000000),((-13695846599772004217584699:ℚ)/38687500000000000000000000),((-1383793352675552410672281:ℚ)/2432000000000000000000000)⟩
theorem valid15 : Valid source35 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source35 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1857:ℚ)/2560) :=
  cell_of_packet source35 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1857:ℚ)/2560),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((5893906247:ℚ)/10000000000),((3008360863:ℚ)/5000000000),((21905718741:ℚ)/23260000000),(1:ℚ),((9519843613:ℚ)/10000000000),((2381116311:ℚ)/2500000000),((622285377:ℚ)/2000000000),((213521099:ℚ)/312500000),((-643541892939666303052589907:ℚ)/1817187500000000000000000000),((-105103394029563539914335051:ℚ)/184832000000000000000000000)⟩
theorem valid16 : Valid source35 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source35 nn0 nn1 Qcell ((1857:ℚ)/2560) ((1163:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((1163:ℚ)/1600),((9323:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((2954374999:ℚ)/5000000000),((6031595143:ℚ)/10000000000),((10975124997:ℚ)/11653750000),(1:ℚ),((2378817769:ℚ)/2500000000),((4759921809:ℚ)/5000000000),((156316407:ℚ)/500000000),((1360335891:ℚ)/2000000000),((-20642857194876094674697786467:ℚ)/58268750000000000000000000000),((-1382087034733309529422281:ℚ)/2432000000000000000000000)⟩
theorem valid17 : Valid source35 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source35 nn0 nn1 Qcell ((1163:ℚ)/1600) ((9323:ℚ)/12800) :=
  cell_of_packet source35 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((9323:ℚ)/12800),((4671:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((1480898437:ℚ)/2500000000),((151161711:ℚ)/250000000),((1832898437:ℚ)/1946250000),(1:ℚ),((148605427:ℚ)/156250000),((9515271081:ℚ)/10000000000),((98156347:ℚ)/312500000),((6770564521:ℚ)/10000000000),((-13794879891043027018263238093:ℚ)/38925000000000000000000000000),((-345309067792860478742289:ℚ)/608000000000000000000000)⟩
theorem valid18 : Valid source35 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source35 nn0 nn1 Qcell ((9323:ℚ)/12800) ((4671:ℚ)/6400) :=
  cell_of_packet source35 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((4671:ℚ)/6400),((9361:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((2969218749:ℚ)/5000000000),((1212268323:ℚ)/2000000000),((479115489:ℚ)/508750000),(1:ℚ),((1188284009:ℚ)/1250000000),((9510747333:ℚ)/10000000000),((157772791:ℚ)/500000000),((6739328673:ℚ)/10000000000),((-3607257146075084211723359607:ℚ)/10175000000000000000000000000),((-1380387104681972851297281:ℚ)/2432000000000000000000000)⟩
theorem valid19 : Valid source35 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source35 nn0 nn1 Qcell ((4671:ℚ)/6400) ((9361:ℚ)/12800) :=
  cell_of_packet source35 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((9361:ℚ)/12800),((469:ℚ)/640),((15:ℚ)/16),(1:ℚ),((186040039:ℚ)/312500000),((379763417:ℚ)/625000000),((690120117:ℚ)/732812500),(1:ℚ),((9501845013:ℚ)/10000000000),((9506272077:ℚ)/10000000000),((792422551:ℚ)/2500000000),((3353985091:ℚ)/5000000000),((-4158216707988044372011520709:ℚ)/11725000000000000000000000000),((-5388826308071149759401:ℚ)/9500000000000000000000)⟩
theorem valid20 : Valid source35 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source35 nn0 nn1 Qcell ((9361:ℚ)/12800) ((469:ℚ)/640) :=
  cell_of_packet source35 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((469:ℚ)/640),((9399:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((2984062499:ℚ)/5000000000),((609108761:ℚ)/1000000000),((3688062499:ℚ)/3916250000),(1:ℚ),((474873293:ℚ)/500000000),((4750922509:ℚ)/5000000000),((636742009:ℚ)/2000000000),((83456091:ℚ)/125000000),((-6946794923705516232993946157:ℚ)/19581250000000000000000000000),((-1378693561823838376297281:ℚ)/2432000000000000000000000)⟩
theorem valid21 : Valid source35 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source35 nn0 nn1 Qcell ((469:ℚ)/640) ((9399:ℚ)/12800) :=
  cell_of_packet source35 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((9399:ℚ)/12800),((4709:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((5982968747:ℚ)/10000000000),((6105960429:ℚ)/10000000000),((22172906241:ℚ)/23545000000),(1:ℚ),((9493134321:ℚ)/10000000000),((1899493173:ℚ)/2000000000),((1598759513:ℚ)/5000000000),((83060977:ℚ)/125000000),((-1671170588832446916592229349:ℚ)/4709000000000000000000000000),((-104716538098897459948710051:ℚ)/184832000000000000000000000)⟩
theorem valid22 : Valid source35 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source35 nn0 nn1 Qcell ((9399:ℚ)/12800) ((4709:ℚ)/6400) :=
  cell_of_packet source35 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((4709:ℚ)/6400),((9437:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((2998906249:ℚ)/5000000000),((6120833131:ℚ)/10000000000),((11108718747:ℚ)/11796250000),(1:ℚ),((948885011:ℚ)/1000000000),((4746567163:ℚ)/5000000000),((802780177:ℚ)/2500000000),((3306570483:ℚ)/5000000000),((-20938826404326783952109230077:ℚ)/58981250000000000000000000000),((-1377006405859890104422281:ℚ)/2432000000000000000000000)⟩
theorem valid23 : Valid source35 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source35 nn0 nn1 Qcell ((4709:ℚ)/6400) ((9437:ℚ)/12800) :=
  cell_of_packet source35 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((9437:ℚ)/12800),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((751582031:ℚ)/1250000000),((1533926429:ℚ)/2500000000),((927582031:ℚ)/985000000),(1:ℚ),((4742306471:ℚ)/5000000000),((1897770023:ℚ)/2000000000),((806129637:ℚ)/2500000000),((1645318453:ℚ)/2500000000),((-69959889898710734061041117:ℚ)/197000000000000000000000000),((-86010326421185862166041:ℚ)/152000000000000000000000)⟩
theorem valid24 : Valid source35 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source35 nn0 nn1 Qcell ((9437:ℚ)/12800) ((591:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((591:ℚ)/800),((379:ℚ)/512),((15:ℚ)/16),(1:ℚ),((3013749999:ℚ)/5000000000),((3075289093:ℚ)/5000000000),((11153249997:ℚ)/11843750000),(1:ℚ),((2370105633:ℚ)/2500000000),((9484612947:ℚ)/10000000000),((323771591:ℚ)/1000000000),((6549274757:ℚ)/10000000000),((-3365928662263642132556893899:ℚ)/9475000000000000000000000000),((-1375325635992752035672281:ℚ)/2432000000000000000000000)⟩
theorem valid25 : Valid source35 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((379:ℚ)/512) :=
  cell_of_packet source35 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((379:ℚ)/512),((4747:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((1510585937:ℚ)/2500000000),((308272527:ℚ)/500000000),((5587757811:ℚ)/5933750000),(1:ℚ),((9476278601:ℚ)/10000000000),((9480422537:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((6517141819:ℚ)/10000000000),((-42172175989732068332429427987:ℚ)/118675000000000000000000000000),((-343621911430224206867289:ℚ)/608000000000000000000000)⟩
theorem valid26 : Valid source35 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source35 nn0 nn1 Qcell ((379:ℚ)/512) ((4747:ℚ)/6400) :=
  cell_of_packet source35 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((4747:ℚ)/6400),((9513:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((3028593749:ℚ)/5000000000),((6180322779:ℚ)/10000000000),((3732593749:ℚ)/3963750000),(1:ℚ),((947218087:ℚ)/1000000000),((4738139303:ℚ)/5000000000),((1631761061:ℚ)/5000000000),((6484872967:ℚ)/10000000000),((-7045022870445731477169872651:ℚ)/19818750000000000000000000000),((-1373651251823736170047281:ℚ)/2432000000000000000000000)⟩
theorem valid27 : Valid source35 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source35 nn0 nn1 Qcell ((4747:ℚ)/6400) ((9513:ℚ)/12800) :=
  cell_of_packet source35 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((9513:ℚ)/12800),((2383:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((379501953:ℚ)/625000000),((1239038981:ℚ)/2000000000),((1402505859:ℚ)/1489375000),(1:ℚ),((9468129063:ℚ)/10000000000),((75777447:ℚ)/80000000),((3276137213:ℚ)/10000000000),((6452466121:ℚ)/10000000000),((-1355775748216303438230423:ℚ)/3812800000000000000000000),((-21450257095342594740729:ℚ)/38000000000000000000000)⟩
theorem valid28 : Valid source35 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source35 nn0 nn1 Qcell ((9513:ℚ)/12800) ((2383:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨((2383:ℚ)/3200),((9551:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((3043437499:ℚ)/5000000000),((3105033459:ℚ)/5000000000),((11242312497:ℚ)/11938750000),(1:ℚ),((1892824581:ℚ)/2000000000),((2367032267:ℚ)/2500000000),((328856431:ℚ)/1000000000),((128398383:ℚ)/200000000),((-5308217608364741485006892751:ℚ)/14923437500000000000000000000),((-1371983252555466507547281:ℚ)/2432000000000000000000000)⟩
theorem valid29 : Valid source35 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source35 nn0 nn1 Qcell ((2383:ℚ)/3200) ((9551:ℚ)/12800) :=
  cell_of_packet source35 nn0 nn1 packet29 valid29
def packet30 : Packet := ⟨((9551:ℚ)/12800),((957:ℚ)/1280),((15:ℚ)/16),(1:ℚ),((6101718747:ℚ)/10000000000),((6224938817:ℚ)/10000000000),((7509718747:ℚ)/7975000000),(1:ℚ),((75681297:ℚ)/80000000),((946412291:ℚ)/1000000000),((1650403157:ℚ)/5000000000),((51097839:ℚ)/80000000),((-28375589048402792028552751:ℚ)/79750000000000000000000000),((-104207525190250566786210051:ℚ)/184832000000000000000000000)⟩
theorem valid30 : Valid source35 packet30 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf30 :
    CellBound source35 nn0 nn1 Qcell ((9551:ℚ)/12800) ((957:ℚ)/1280) :=
  cell_of_packet source35 nn0 nn1 packet30 valid30
def packet31 : Packet := ⟨((957:ℚ)/1280),((9589:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((3058281249:ℚ)/5000000000),((1247962121:ℚ)/2000000000),((11286843747:ℚ)/11986250000),(1:ℚ),((9456246453:ℚ)/10000000000),((946016213:ℚ)/1000000000),((3312866051:ℚ)/10000000000),((6354396051:ℚ)/10000000000),((-853218408301825961972348469:ℚ)/2397250000000000000000000000),((-1370321637988599048172281:ℚ)/2432000000000000000000000)⟩
theorem valid31 : Valid source35 packet31 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf31 :
    CellBound source35 nn0 nn1 Qcell ((957:ℚ)/1280) ((9589:ℚ)/12800) :=
  cell_of_packet source35 nn0 nn1 packet31 valid31
def packet32 : Packet := ⟨((9589:ℚ)/12800),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((766425781:ℚ)/1250000000),((3127341141:ℚ)/5000000000),((2827277343:ℚ)/3002500000),(1:ℚ),((4726187811:ℚ)/5000000000),((4728123229:ℚ)/5000000000),((831186567:ℚ)/2500000000),((6321415391:ℚ)/10000000000),((-2672396969844227237172503169:ℚ)/7506250000000000000000000000),((-85593326541823446541041:ℚ)/152000000000000000000000)⟩
theorem valid32 : Valid source35 packet32 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf32 :
    CellBound source35 nn0 nn1 Qcell ((9589:ℚ)/12800) ((1201:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet32 valid32
def packet33 : Packet := ⟨((1201:ℚ)/1600),((4823:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3073124999:ℚ)/5000000000),((1256885061:ℚ)/2000000000),((11331374997:ℚ)/12057500000),(1:ℚ),((9444767421:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1673989387:ℚ)/5000000000),((6288285543:ℚ)/10000000000),((-42828259854491042426182089303:ℚ)/120575000000000000000000000000),((-1367184139463653791922281:ℚ)/2432000000000000000000000)⟩
theorem valid33 : Valid source35 packet33 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf33 :
    CellBound source35 nn0 nn1 Qcell ((1201:ℚ)/1600) ((4823:ℚ)/6400) :=
  cell_of_packet source35 nn0 nn1 packet33 valid33
def packet34 : Packet := ⟨((4823:ℚ)/6400),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3087968749:ℚ)/5000000000),((631416789:ℚ)/1000000000),((1263989583:ℚ)/1345000000),(1:ℚ),((4718667711:ℚ)/5000000000),((4722383713:ℚ)/5000000000),((674104879:ℚ)/2000000000),((6221568569:ℚ)/10000000000),((-597536751235821490650709749:ℚ)/1681250000000000000000000000),((-1365535314034646738797281:ℚ)/2432000000000000000000000)⟩
theorem valid34 : Valid source35 packet34 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf34 :
    CellBound source35 nn0 nn1 Qcell ((4823:ℚ)/6400) ((2421:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet34 valid34
def packet35 : Packet := ⟨((2421:ℚ)/3200),((4861:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3102812499:ℚ)/5000000000),((1585977511:ℚ)/2500000000),((11420437497:ℚ)/12152500000),(1:ℚ),((235751939:ℚ)/250000000),((9437335427:ℚ)/10000000000),((339240263:ℚ)/1000000000),((384639067:ℚ)/625000000),((-43216610405168941503168483021:ℚ)/121525000000000000000000000000),((-1363892871213929888797281:ℚ)/2432000000000000000000000)⟩
theorem valid35 : Valid source35 packet35 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf35 :
    CellBound source35 nn0 nn1 Qcell ((2421:ℚ)/3200) ((4861:ℚ)/6400) :=
  cell_of_packet source35 nn0 nn1 packet35 valid35
def packet36 : Packet := ⟨((4861:ℚ)/6400),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3117656249:ℚ)/5000000000),((6373651771:ℚ)/10000000000),((11464968747:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((1886015513:ℚ)/2000000000),((1706816001:ℚ)/5000000000),((6086233921:ℚ)/10000000000),((-21705076944234168547407381:ℚ)/61000000000000000000000000),((-1362256810602815241922281:ℚ)/2432000000000000000000000)⟩
theorem valid36 : Valid source35 packet36 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf36 :
    CellBound source35 nn0 nn1 Qcell ((4861:ℚ)/6400) ((61:ℚ)/80) :=
  cell_of_packet source35 nn0 nn1 packet36 valid36
def packet37 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((6264999997:ℚ)/10000000000),((1286626793:ℚ)/2000000000),((23018999991:ℚ)/24590000000),(1:ℚ),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((240702913:ℚ)/400000000),((-5443605002219277868040324979:ℚ)/15368750000000000000000000000),((-103182372630479706992460051:ℚ)/184832000000000000000000000)⟩
theorem valid37 : Valid source35 packet37 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf37 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet37 valid37
def packet38 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3162187499:ℚ)/5000000000),((6492614511:ℚ)/10000000000),((3866187499:ℚ)/4130000000),(1:ℚ),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((1175629057:ℚ)/2000000000),((-3661168028146923890509489813:ℚ)/10325000000000000000000000000),((-1354422664686772520047281:ℚ)/2432000000000000000000000)⟩
theorem valid38 : Valid source35 packet38 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf38 :
    CellBound source35 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet38 valid38
def packet39 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3191874999:ℚ)/5000000000),((6611570807:ℚ)/10000000000),((11687624997:ℚ)/12580000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((5735737281:ℚ)/10000000000),((-5396650310076986573820621:ℚ)/15356445312500000000000000),((-1345279823203643054422281:ℚ)/2432000000000000000000000)⟩
theorem valid39 : Valid source35 packet39 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf39 :
    CellBound source35 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet39 valid39
def packet40 : Packet := ⟨((629:ℚ)/800),((1277:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3251249999:ℚ)/5000000000),((134610419:ℚ)/200000000),((11865749997:ℚ)/12770000000),(1:ℚ),((2337671911:ℚ)/2500000000),((9372267491:ℚ)/10000000000),((181171659:ℚ)/500000000),((5441027351:ℚ)/10000000000),((-11243001839721348103407902733:ℚ)/31925000000000000000000000000),((-1338927441250010560672281:ℚ)/2432000000000000000000000)⟩
theorem valid40 : Valid source35 packet40 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf40 :
    CellBound source35 nn0 nn1 Qcell ((629:ℚ)/800) ((1277:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet40 valid40
def packet41 : Packet := ⟨((1277:ℚ)/1600),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((3310624999:ℚ)/5000000000),((6849465209:ℚ)/10000000000),((1338208333:ℚ)/1440000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9350687649:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1026240181:ℚ)/2000000000),((-79388834731137261139340881:ℚ)/225000000000000000000000000),((-1332677080160957316922281:ℚ)/2432000000000000000000000)⟩
theorem valid41 : Valid source35 packet41 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf41 :
    CellBound source35 nn0 nn1 Qcell ((1277:ℚ)/1600) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet41 valid41
def packet42 : Packet := ⟨((81:ℚ)/100),((343:ℚ)/400),((15:ℚ)/16),(1:ℚ),((3369999999:ℚ)/5000000000),((3662594161:ℚ)/5000000000),((12221999997:ℚ)/13720000000),(1:ℚ),((57977633:ℚ)/62500000),((2332870371:ℚ)/2500000000),((1913736159:ℚ)/5000000000),((4803308277:ℚ)/10000000000),((-179057770686833206057880967:ℚ)/535937500000000000000000000),((-1290967291530547323172281:ℚ)/2432000000000000000000000)⟩
theorem valid42 : Valid source35 packet42 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf42 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((343:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet42 valid42
def packet43 : Packet := ⟨((343:ℚ)/400),((181:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3607499999:ℚ)/5000000000),((1950208843:ℚ)/2500000000),((12934499997:ℚ)/14480000000),(1:ℚ),((9252071821:ℚ)/10000000000),((1855284257:ℚ)/2000000000),((1946075537:ℚ)/5000000000),((399575839:ℚ)/1250000000),((-60974283495530928231299421:ℚ)/181000000000000000000000000),((-67758765676860413061699:ℚ)/128000000000000000000000)⟩
theorem valid43 : Valid source35 packet43 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf43 :
    CellBound source35 nn0 nn1 Qcell ((343:ℚ)/400) ((181:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet43 valid43
def packet44 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((15:ℚ)/16),(1:ℚ),((3844999999:ℚ)/5000000000),((1093993093:ℚ)/1250000000),((13646999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-1978959346352142701966409:ℚ)/6250000000000000000000000),((-1376769:ℚ)/2560000)⟩
theorem valid44 : Valid source35 packet44 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf44 :
    CellBound source35 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet44 valid44
def packet45 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4319999999:ℚ)/5000000000),((12554853183:ℚ)/10000000000),((5023999999:ℚ)/7360000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-967920199687:ℚ)/4600000000000),((-1376769:ℚ)/2560000)⟩
theorem valid45 : Valid source35 packet45 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf45 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet45 valid45
private theorem node0_2 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((2231:ℚ)/3200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source35 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source35 nn0 nn1 Qcell ((4557:ℚ)/6400) ((919:ℚ)/1280) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source35 nn0 nn1 Qcell ((2269:ℚ)/3200) ((919:ℚ)/1280) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source35 nn0 nn1 Qcell ((2231:ℚ)/3200) ((919:ℚ)/1280) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((919:ℚ)/1280) :=
  cell_join node0_5 node5_11
private theorem node12_14 :
    CellBound source35 nn0 nn1 Qcell ((9209:ℚ)/12800) ((9247:ℚ)/12800) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source35 nn0 nn1 Qcell ((919:ℚ)/1280) ((9247:ℚ)/12800) :=
  cell_join leaf11 node12_14
private theorem node15_17 :
    CellBound source35 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source35 nn0 nn1 Qcell ((9247:ℚ)/12800) ((1163:ℚ)/1600) :=
  cell_join leaf14 node15_17
private theorem node11_17 :
    CellBound source35 nn0 nn1 Qcell ((919:ℚ)/1280) ((1163:ℚ)/1600) :=
  cell_join node11_14 node14_17
private theorem node18_20 :
    CellBound source35 nn0 nn1 Qcell ((9323:ℚ)/12800) ((9361:ℚ)/12800) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source35 nn0 nn1 Qcell ((1163:ℚ)/1600) ((9361:ℚ)/12800) :=
  cell_join leaf17 node18_20
private theorem node21_23 :
    CellBound source35 nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound source35 nn0 nn1 Qcell ((9361:ℚ)/12800) ((4709:ℚ)/6400) :=
  cell_join leaf20 node21_23
private theorem node17_23 :
    CellBound source35 nn0 nn1 Qcell ((1163:ℚ)/1600) ((4709:ℚ)/6400) :=
  cell_join node17_20 node20_23
private theorem node11_23 :
    CellBound source35 nn0 nn1 Qcell ((919:ℚ)/1280) ((4709:ℚ)/6400) :=
  cell_join node11_17 node17_23
private theorem node0_23 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((4709:ℚ)/6400) :=
  cell_join node0_11 node11_23
private theorem node23_25 :
    CellBound source35 nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_join leaf23 leaf24
private theorem node26_28 :
    CellBound source35 nn0 nn1 Qcell ((379:ℚ)/512) ((9513:ℚ)/12800) :=
  cell_join leaf26 leaf27
private theorem node25_28 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((9513:ℚ)/12800) :=
  cell_join leaf25 node26_28
private theorem node23_28 :
    CellBound source35 nn0 nn1 Qcell ((4709:ℚ)/6400) ((9513:ℚ)/12800) :=
  cell_join node23_25 node25_28
private theorem node29_31 :
    CellBound source35 nn0 nn1 Qcell ((2383:ℚ)/3200) ((957:ℚ)/1280) :=
  cell_join leaf29 leaf30
private theorem node28_31 :
    CellBound source35 nn0 nn1 Qcell ((9513:ℚ)/12800) ((957:ℚ)/1280) :=
  cell_join leaf28 node29_31
private theorem node32_34 :
    CellBound source35 nn0 nn1 Qcell ((9589:ℚ)/12800) ((4823:ℚ)/6400) :=
  cell_join leaf32 leaf33
private theorem node31_34 :
    CellBound source35 nn0 nn1 Qcell ((957:ℚ)/1280) ((4823:ℚ)/6400) :=
  cell_join leaf31 node32_34
private theorem node28_34 :
    CellBound source35 nn0 nn1 Qcell ((9513:ℚ)/12800) ((4823:ℚ)/6400) :=
  cell_join node28_31 node31_34
private theorem node23_34 :
    CellBound source35 nn0 nn1 Qcell ((4709:ℚ)/6400) ((4823:ℚ)/6400) :=
  cell_join node23_28 node28_34
private theorem node35_37 :
    CellBound source35 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf35 leaf36
private theorem node34_37 :
    CellBound source35 nn0 nn1 Qcell ((4823:ℚ)/6400) ((61:ℚ)/80) :=
  cell_join leaf34 node35_37
private theorem node38_40 :
    CellBound source35 nn0 nn1 Qcell ((2459:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join leaf38 leaf39
private theorem node37_40 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf37 node38_40
private theorem node34_40 :
    CellBound source35 nn0 nn1 Qcell ((4823:ℚ)/6400) ((629:ℚ)/800) :=
  cell_join node34_37 node37_40
private theorem node41_43 :
    CellBound source35 nn0 nn1 Qcell ((1277:ℚ)/1600) ((343:ℚ)/400) :=
  cell_join leaf41 leaf42
private theorem node40_43 :
    CellBound source35 nn0 nn1 Qcell ((629:ℚ)/800) ((343:ℚ)/400) :=
  cell_join leaf40 node41_43
private theorem node44_46 :
    CellBound source35 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf44 leaf45
private theorem node43_46 :
    CellBound source35 nn0 nn1 Qcell ((343:ℚ)/400) ((69:ℚ)/50) :=
  cell_join leaf43 node44_46
private theorem node40_46 :
    CellBound source35 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node40_43 node43_46
private theorem node34_46 :
    CellBound source35 nn0 nn1 Qcell ((4823:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node34_40 node40_46
private theorem node23_46 :
    CellBound source35 nn0 nn1 Qcell ((4709:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node23_34 node34_46
private theorem node0_46 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_23 node23_46
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_46
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29,packet30,packet31,packet32,packet33,packet34,packet35,packet36,packet37,packet38,packet39,packet40,packet41,packet42,packet43,packet44,packet45]
theorem packet_count : packets.length = 46 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC32
#check @N11Formalization.C450Source35GroupedC32.bound
#print axioms N11Formalization.C450Source35GroupedC32.valid0
#print axioms N11Formalization.C450Source35GroupedC32.valid1
#print axioms N11Formalization.C450Source35GroupedC32.valid2
#print axioms N11Formalization.C450Source35GroupedC32.valid3
#print axioms N11Formalization.C450Source35GroupedC32.valid4
#print axioms N11Formalization.C450Source35GroupedC32.valid5
#print axioms N11Formalization.C450Source35GroupedC32.valid6
#print axioms N11Formalization.C450Source35GroupedC32.valid7
#print axioms N11Formalization.C450Source35GroupedC32.valid8
#print axioms N11Formalization.C450Source35GroupedC32.valid9
#print axioms N11Formalization.C450Source35GroupedC32.valid10
#print axioms N11Formalization.C450Source35GroupedC32.valid11
#print axioms N11Formalization.C450Source35GroupedC32.valid12
#print axioms N11Formalization.C450Source35GroupedC32.valid13
#print axioms N11Formalization.C450Source35GroupedC32.valid14
#print axioms N11Formalization.C450Source35GroupedC32.valid15
#print axioms N11Formalization.C450Source35GroupedC32.valid16
#print axioms N11Formalization.C450Source35GroupedC32.valid17
#print axioms N11Formalization.C450Source35GroupedC32.valid18
#print axioms N11Formalization.C450Source35GroupedC32.valid19
#print axioms N11Formalization.C450Source35GroupedC32.valid20
#print axioms N11Formalization.C450Source35GroupedC32.valid21
#print axioms N11Formalization.C450Source35GroupedC32.valid22
#print axioms N11Formalization.C450Source35GroupedC32.valid23
#print axioms N11Formalization.C450Source35GroupedC32.valid24
#print axioms N11Formalization.C450Source35GroupedC32.valid25
#print axioms N11Formalization.C450Source35GroupedC32.valid26
#print axioms N11Formalization.C450Source35GroupedC32.valid27
#print axioms N11Formalization.C450Source35GroupedC32.valid28
#print axioms N11Formalization.C450Source35GroupedC32.valid29
#print axioms N11Formalization.C450Source35GroupedC32.valid30
#print axioms N11Formalization.C450Source35GroupedC32.valid31
#print axioms N11Formalization.C450Source35GroupedC32.valid32
#print axioms N11Formalization.C450Source35GroupedC32.valid33
#print axioms N11Formalization.C450Source35GroupedC32.valid34
#print axioms N11Formalization.C450Source35GroupedC32.valid35
#print axioms N11Formalization.C450Source35GroupedC32.valid36
#print axioms N11Formalization.C450Source35GroupedC32.valid37
#print axioms N11Formalization.C450Source35GroupedC32.valid38
#print axioms N11Formalization.C450Source35GroupedC32.valid39
#print axioms N11Formalization.C450Source35GroupedC32.valid40
#print axioms N11Formalization.C450Source35GroupedC32.valid41
#print axioms N11Formalization.C450Source35GroupedC32.valid42
#print axioms N11Formalization.C450Source35GroupedC32.valid43
#print axioms N11Formalization.C450Source35GroupedC32.valid44
#print axioms N11Formalization.C450Source35GroupedC32.valid45
#print axioms N11Formalization.C450Source35GroupedC32.bound
#print axioms N11Formalization.C450Source35GroupedC32.endpoint_checks
