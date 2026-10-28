import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((3155949789:ℚ)/5000000000),((3315888749:ℚ)/5000000000),((-995888749:ℚ)/12400000000),((132150633:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5907680837:ℚ)/10000000000),((33437955838809555508478261323658749:ℚ)/476656000000000000000000000000000000),((-314502828601436896892933911:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((6553359253:ℚ)/10000000000),((6752473487:ℚ)/10000000000),((-2112473487:ℚ)/25750000000),((-460077759:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5310335573:ℚ)/10000000000),((32306901022501314930262907071916708666884127978970519255261:ℚ)/458693650637435913085937500000000000000000000000000000000000),((-1462324471468086426777281319:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((3336989469:ℚ)/5000000000),((6873098587:ℚ)/10000000000),((-2233098587:ℚ)/26225000000),((-136989469:ℚ)/17800000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4988044259:ℚ)/10000000000),((64251316991774857610010774409285530095794039427840084885921:ℚ)/892907603586816406250000000000000000000000000000000000000000),((-391335885394928896099660951:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/4),((-3:ℚ)/16),((6794530577:ℚ)/10000000000),((3466692881:ℚ)/5000000000),((-1146692881:ℚ)/13350000000),((-1183591731:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2322817901:ℚ)/5000000000),((22121585858121675220103043321860184261607590241347995517307:ℚ)/306927530646093750000000000000000000000000000000000000000000),((-1668940700507874533872559039:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((3427391019:ℚ)/5000000000),((6993656631:ℚ)/10000000000),((-2353656631:ℚ)/26937500000),((-682173057:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2232719513:ℚ)/5000000000),((10508791175556950822058147813253610712532768735986036562723693:ℚ)/144348065510374450683593750000000000000000000000000000000000000),((-1191798288489521348680591:ℚ)/10240000000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((1383003569:ℚ)/2000000000),((705391163:ℚ)/1000000000),((-241391163:ℚ)/2717500000),((-103003569:ℚ)/7310000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4278238527:ℚ)/10000000000),((307952841027006866465399863690017727512206956611857146329:ℚ)/4188933316336566162109375000000000000000000000000000000000),((-70924722337834766208218751:ℚ)/591462400000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((1395047683:ℚ)/2000000000),((7114151179:ℚ)/10000000000),((-2474151179:ℚ)/27412500000),((-345143049:ℚ)/22120000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2041532803:ℚ)/5000000000),((7550380803087651988545870420820816384902685493595883515179:ℚ)/101733795843493652343750000000000000000000000000000000000000),((-73016997162277704444374999:ℚ)/591462400000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((879430519:ℚ)/1250000000),((7234585539:ℚ)/10000000000),((-370655077:ℚ)/3950000000),((-79430519:ℚ)/4687500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((969677821:ℚ)/2500000000),((88050218136066644270090637627385899159815927042691853:ℚ)/1155560156250000000000000000000000000000000000000000000),((-29341837069442080265534351:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((286232507:ℚ)/400000000),((1470992559:ℚ)/2000000000),((-542992559:ℚ)/5625000000),((-90697521:ℚ)/4576000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3435813171:ℚ)/10000000000),((7255821930201858819214133354769857862305299695422965039:ℚ)/93608093261718750000000000000000000000000000000000000000),((-3173153707872428581701959:ℚ)/23658496000000000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((7276126369:ℚ)/10000000000),((3797778649:ℚ)/5000000000),((-1477778649:ℚ)/14300000000),((-876126369:ℚ)/39400000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2929884341:ℚ)/10000000000),((14409228101268945170680771886804831626288834936094476124403:ℚ)/177321171035937500000000000000000000000000000000000000000000),((-2089150239648436712651381151:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((7516600113:ℚ)/10000000000),((7835955483:ℚ)/10000000000),((-3195955483:ℚ)/29550000000),((-3349800339:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1482821537:ℚ)/10000000000),((5573873287717192176325752111350639812041433630847838212209:ℚ)/66676014686718750000000000000000000000000000000000000000000),((-2302771841085386245614404479:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((3878442667:ℚ)/5000000000),((2079058383:ℚ)/2500000000),((-919058383:ℚ)/7625000000),((-678442667:ℚ)/21600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((15213170490339374528937474752298844984729651570023845923:ℚ)/168323922729492187500000000000000000000000000000000000000),((-164643357:ℚ)/1024000000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((329478319:ℚ)/400000000),((10232270639:ℚ)/10000000000),((-1864090213:ℚ)/10800000000),((-220434957:ℚ)/6400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2179165354651741050976349521137788057218055135384317:ℚ)/18225000000000000000000000000000000000000000000000000),((-164643357:ℚ)/1024000000)⟩
theorem valid12 : Valid source31 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((2030474647:ℚ)/2000000000),((7025499983:ℚ)/5000000000),((-4705499983:ℚ)/20000000000),((-750474647:ℚ)/14720000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((171743149176049439798104716264452636023:ℚ)/1058000000000000000000000000000000000000),((-164643357:ℚ)/1024000000)⟩
theorem valid13 : Valid source31 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC13
#check @N11Formalization.C450Source31GroupedC13.bound
#print axioms N11Formalization.C450Source31GroupedC13.valid0
#print axioms N11Formalization.C450Source31GroupedC13.valid1
#print axioms N11Formalization.C450Source31GroupedC13.valid2
#print axioms N11Formalization.C450Source31GroupedC13.valid3
#print axioms N11Formalization.C450Source31GroupedC13.valid4
#print axioms N11Formalization.C450Source31GroupedC13.valid5
#print axioms N11Formalization.C450Source31GroupedC13.valid6
#print axioms N11Formalization.C450Source31GroupedC13.valid7
#print axioms N11Formalization.C450Source31GroupedC13.valid8
#print axioms N11Formalization.C450Source31GroupedC13.valid9
#print axioms N11Formalization.C450Source31GroupedC13.valid10
#print axioms N11Formalization.C450Source31GroupedC13.valid11
#print axioms N11Formalization.C450Source31GroupedC13.valid12
#print axioms N11Formalization.C450Source31GroupedC13.valid13
#print axioms N11Formalization.C450Source31GroupedC13.bound
#print axioms N11Formalization.C450Source31GroupedC13.endpoint_checks
