import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC16
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((-1:ℚ)/16),(0:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/16),(0:ℚ),((1239070619:ℚ)/2000000000),((1337140173:ℚ)/2000000000),((-697140173:ℚ)/19840000000),((6:ℚ)/155),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6177598167:ℚ)/10000000000),((47829615367310519:ℚ)/4766560000000000000),((-1506734253564218481620933:ℚ)/221798400000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((1334136799:ℚ)/2000000000),((3402263029:ℚ)/5000000000),((-600754343:ℚ)/17800000000),((16:ℚ)/445),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4997099587:ℚ)/10000000000),((2010452885640107271052648008497:ℚ)/206533886718750000000000000000000),((-3775367235081209770106119:ℚ)/462080000000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((1697377371:ℚ)/2500000000),((3461674333:ℚ)/5000000000),((-1861674333:ℚ)/54350000000),((192:ℚ)/5435),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2330180101:ℚ)/5000000000),((2372406578688363681617305597179:ℚ)/244973278617858886718750000000000),((-3929486966879868657992951:ℚ)/462080000000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/16),(0:ℚ),((863541547:ℚ)/1250000000),((6982759041:ℚ)/10000000000),((-3782759041:ℚ)/110600000000),((96:ℚ)/2765),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((2149695901:ℚ)/5000000000),((11359793711954778506263415592039:ℚ)/1179634326171875000000000000000000),((-49042138971234733776895037:ℚ)/5544960000000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/16),(0:ℚ),((696774289:ℚ)/1000000000),((3521084409:ℚ)/5000000000),((-1921084409:ℚ)/55775000000),((384:ℚ)/11155),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4107833899:ℚ)/10000000000),((56628117197895752498106932801529:ℚ)/5893603723144531250000000000000000),((-12491492345405720714504237:ℚ)/1386240000000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/16),(0:ℚ),((1756788201:ℚ)/2500000000),((1775394503:ℚ)/2500000000),((-108377167:ℚ)/3125000000),((64:ℚ)/1875),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((3907455093:ℚ)/10000000000),((12343877851176126665932209809791:ℚ)/1287460327148437500000000000000000),((-1060196861279210557758031:ℚ)/115520000000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/16),(0:ℚ),((1771640533:ℚ)/2500000000),((3580493319:ℚ)/5000000000),((-1980493319:ℚ)/56725000000),((384:ℚ)/11345),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3696817411:ℚ)/10000000000),((54575210072915929408276557909643:ℚ)/5703921439941406250000000000000000),((-12953144769355172009121197:ℚ)/1386240000000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/16),(0:ℚ),((714597089:ℚ)/1000000000),((722039471:ℚ)/1000000000),((-402039471:ℚ)/11440000000),((24:ℚ)/715),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3474051211:ℚ)/10000000000),((1363455177019704969936164222817:ℚ)/142783544921875000000000000000000),((-175784529497784908201119:ℚ)/18483200000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((1801344773:ℚ)/2500000000),((7279802241:ℚ)/10000000000),((-4079802241:ℚ)/115350000000),((128:ℚ)/3845),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3236648831:ℚ)/10000000000),((6349064380301720347934785797743:ℚ)/666147376464843750000000000000000),((-53657788884729919575179837:ℚ)/5544960000000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-1:ℚ)/16),(0:ℚ),((29059147:ℚ)/40000000),((1834802311:ℚ)/2500000000),((-1034802311:ℚ)/29075000000),((192:ℚ)/5815),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((119244439:ℚ)/400000000),((91341974333330033726774839394047:ℚ)/9601060467529296875000000000000000),((-1137080612050698168013039:ℚ)/115520000000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((7324193879:ℚ)/10000000000),((7398615733:ℚ)/10000000000),((-4198615733:ℚ)/117250000000),((384:ℚ)/11725),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((108091703:ℚ)/400000000),((186872706595313646132664935620319:ℚ)/19676534461975097656250000000000000),((-18500533524315015788004551:ℚ)/1848320000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((7383600491:ℚ)/10000000000),((3758713607:ℚ)/5000000000),((-2158713607:ℚ)/59100000000),((32:ℚ)/985),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2392061021:ℚ)/10000000000),((3542474150686400791154852521651:ℚ)/373309228515625000000000000000000),((-4698332780455074446150991:ℚ)/462080000000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-1:ℚ)/16),(0:ℚ),((3751206107:ℚ)/5000000000),((7636236779:ℚ)/10000000000),((-4436236779:ℚ)/120100000000),((192:ℚ)/6005),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((401062221:ℚ)/2500000000),((400091472357044010029772150635573:ℚ)/42293056665039062500000000000000000),((-5109448187178613:ℚ)/486400000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/16),(0:ℚ),((1905305503:ℚ)/2500000000),((8111457561:ℚ)/10000000000),((-4911457561:ℚ)/122000000000),((48:ℚ)/1525),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((6566182893340896217228373059713:ℚ)/692691040039062500000000000000000),((-345287:ℚ)/32000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/16),(0:ℚ),((8096443661:ℚ)/10000000000),((10012130841:ℚ)/10000000000),((-6812130841:ℚ)/129600000000),((4:ℚ)/135),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((13793903616476483165948206223:ℚ)/1441625976562500000000000000000),((-345287:ℚ)/32000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/16),(0:ℚ),((9997119583:ℚ)/10000000000),((6906460521:ℚ)/5000000000),((-5306460521:ℚ)/80000000000),((3:ℚ)/125),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((207800115991563:ℚ)/20000000000000000),((-345287:ℚ)/32000000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC16
#check @N11Formalization.C450SeventhGroupedC16.bound
#print axioms N11Formalization.C450SeventhGroupedC16.valid0
#print axioms N11Formalization.C450SeventhGroupedC16.valid1
#print axioms N11Formalization.C450SeventhGroupedC16.valid2
#print axioms N11Formalization.C450SeventhGroupedC16.valid3
#print axioms N11Formalization.C450SeventhGroupedC16.valid4
#print axioms N11Formalization.C450SeventhGroupedC16.valid5
#print axioms N11Formalization.C450SeventhGroupedC16.valid6
#print axioms N11Formalization.C450SeventhGroupedC16.valid7
#print axioms N11Formalization.C450SeventhGroupedC16.valid8
#print axioms N11Formalization.C450SeventhGroupedC16.valid9
#print axioms N11Formalization.C450SeventhGroupedC16.valid10
#print axioms N11Formalization.C450SeventhGroupedC16.valid11
#print axioms N11Formalization.C450SeventhGroupedC16.valid12
#print axioms N11Formalization.C450SeventhGroupedC16.valid13
#print axioms N11Formalization.C450SeventhGroupedC16.valid14
#print axioms N11Formalization.C450SeventhGroupedC16.valid15
#print axioms N11Formalization.C450SeventhGroupedC16.bound
#print axioms N11Formalization.C450SeventhGroupedC16.endpoint_checks
