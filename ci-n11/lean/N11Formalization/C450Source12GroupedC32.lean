import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((2879999999:ℚ)/5000000000),((3149274267:ℚ)/5000000000),((9279999997:ℚ)/10680000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((177679089:ℚ)/250000000),((-759978531596111837914301056940848139717285427834611:ℚ)/13218168750000000000000000000000000000000000000000000),((-516575626944745676409131:ℚ)/2166000000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((6234999997:ℚ)/10000000000),((3268049207:ℚ)/5000000000),((19984999991:ℚ)/22120000000),(1:ℚ),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1521738267:ℚ)/2500000000),((-4238759699047567201484956630948864206550070883147737:ℚ)/66059522265625000000000000000000000000000000000000000),((-170370719348924201441457:ℚ)/722000000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3236249999:ℚ)/5000000000),((6773644979:ℚ)/10000000000),((10348749997:ℚ)/11440000000),(1:ℚ),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5516808937:ℚ)/10000000000),((-37541283961206542048304013546157826811634689024060699:ℚ)/584841400000000000000000000000000000000000000000000000),((-674190040017144262597513:ℚ)/2888000000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3354999999:ℚ)/5000000000),((43077607:ℚ)/62500000),((10704999997:ℚ)/11630000000),(1:ℚ),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((611005957:ℚ)/1250000000),((-41350043936628729616932895825634117698833351612887371:ℚ)/614467869921875000000000000000000000000000000000000000),((-26192989794732603257:ℚ)/112812500000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((15:ℚ)/16),(1:ℚ),((3414374999:ℚ)/5000000000),((3475901461:ℚ)/5000000000),((10883124997:ℚ)/11725000000),(1:ℚ),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2272054763:ℚ)/5000000000),((-43334957646542282389720111426514678885683795315019971:ℚ)/629649102783203125000000000000000000000000000000000000),((-167178754240536974156953:ℚ)/722000000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((6888124997:ℚ)/10000000000),((7011188549:ℚ)/10000000000),((21944374991:ℚ)/23640000000),(1:ℚ),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2181372287:ℚ)/5000000000),((-9860862552204892758206330645207869640085470834129857:ℚ)/143350743750000000000000000000000000000000000000000000),((-666888980964385197228793:ℚ)/2888000000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3473749999:ℚ)/5000000000),((883821751:ℚ)/1250000000),((11061249997:ℚ)/11915000000),(1:ℚ),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((417403191:ℚ)/1000000000),((-45430171283303458774943052357599945089699089876625171:ℚ)/660757611669921875000000000000000000000000000000000000),((-10391600477205103824593:ℚ)/45125000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3503437499:ℚ)/5000000000),((71299593:ℚ)/100000000),((11150312497:ℚ)/12010000000),(1:ℚ),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3976922093:ℚ)/10000000000),((-11626000155712100273008731508205123865977392382539039:ℚ)/169172226660156250000000000000000000000000000000000000),((-198970609699803391571:ℚ)/866400000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((7066249997:ℚ)/10000000000),((449334027:ℚ)/625000000),((22478749991:ℚ)/24210000000),(1:ℚ),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((3770094529:ℚ)/10000000000),((-31730362591431537133241185788985700762042194375930651:ℚ)/461916160839843750000000000000000000000000000000000000),((-7750872493687110632891:ℚ)/33843750000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3562812499:ℚ)/5000000000),((1449745881:ℚ)/2000000000),((11328437497:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3551848047:ℚ)/10000000000),((-798442233886574702143482092742599439573187613575819:ℚ)/11628125000000000000000000000000000000000000000000000),((-79149563028048552978419:ℚ)/346560000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((7184999997:ℚ)/10000000000),((456757139:ℚ)/625000000),((22834999991:ℚ)/24590000000),(1:ℚ),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((829981817:ℚ)/2500000000),((-24916236794048043516441971569111539983960243376131537:ℚ)/363007533666992187500000000000000000000000000000000000),((-2569340167318412971353:ℚ)/11281250000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3622187499:ℚ)/5000000000),((7367498893:ℚ)/10000000000),((195026483:ℚ)/210000000),(1:ℚ),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((122849259:ℚ)/400000000),((-27579479118208126555843257297045476666552070221:ℚ)/401953125000000000000000000000000000000000000000),((-655921958808113684725257:ℚ)/2888000000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3651874999:ℚ)/5000000000),((7486267791:ℚ)/10000000000),((11595624997:ℚ)/12580000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2801291589:ℚ)/10000000000),((-13054543817195786734246687967233881248767403306092891:ℚ)/194420460156250000000000000000000000000000000000000000),((-1956786496767910211650499:ℚ)/8664000000000000000000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((3711249999:ℚ)/5000000000),((7723803927:ℚ)/10000000000),((11773749997:ℚ)/12960000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((541372623:ℚ)/2500000000),((-2028531927149198721680846113215939614014958831228297:ℚ)/31492800000000000000000000000000000000000000000000000),((-1797107:ℚ)/8000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((15:ℚ)/16),(1:ℚ),((3829999999:ℚ)/5000000000),((4812015603:ℚ)/5000000000),((12129999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-3786277513867716886972754912546426390955772632775819:ℚ)/100000000000000000000000000000000000000000000000000000),((-1797107:ℚ)/8000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4779999999:ℚ)/5000000000),((1678037249:ℚ)/1250000000),((14979999997:ℚ)/22080000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-153974051434362917214696219999451:ℚ)/6229504000000000000000000000000000),((-1797107:ℚ)/8000000)⟩
theorem valid15 : Valid source12 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source12 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source12 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC32
#check @N11Formalization.C450Source12GroupedC32.bound
#print axioms N11Formalization.C450Source12GroupedC32.valid0
#print axioms N11Formalization.C450Source12GroupedC32.valid1
#print axioms N11Formalization.C450Source12GroupedC32.valid2
#print axioms N11Formalization.C450Source12GroupedC32.valid3
#print axioms N11Formalization.C450Source12GroupedC32.valid4
#print axioms N11Formalization.C450Source12GroupedC32.valid5
#print axioms N11Formalization.C450Source12GroupedC32.valid6
#print axioms N11Formalization.C450Source12GroupedC32.valid7
#print axioms N11Formalization.C450Source12GroupedC32.valid8
#print axioms N11Formalization.C450Source12GroupedC32.valid9
#print axioms N11Formalization.C450Source12GroupedC32.valid10
#print axioms N11Formalization.C450Source12GroupedC32.valid11
#print axioms N11Formalization.C450Source12GroupedC32.valid12
#print axioms N11Formalization.C450Source12GroupedC32.valid13
#print axioms N11Formalization.C450Source12GroupedC32.valid14
#print axioms N11Formalization.C450Source12GroupedC32.valid15
#print axioms N11Formalization.C450Source12GroupedC32.bound
#print axioms N11Formalization.C450Source12GroupedC32.endpoint_checks
