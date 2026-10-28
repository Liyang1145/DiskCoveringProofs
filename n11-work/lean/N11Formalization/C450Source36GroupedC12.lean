import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((3199273839:ℚ)/5000000000),((1653679209:ℚ)/2500000000),((-565679209:ℚ)/4960000000),((-399273839:ℚ)/12637500000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((5699755517:ℚ)/10000000000),((19013267522974054092992682280864399:ℚ)/476656000000000000000000000000000000),((202522300773589450874461:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((1304003261:ℚ)/2000000000),((6736135767:ℚ)/10000000000),((-2384135767:ℚ)/20220000000),((-184003261:ℚ)/5150000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((5396338357:ℚ)/10000000000),((69086468746191499059445996564791741295599669217360183:ℚ)/1614631767187500000000000000000000000000000000000000000),((16092188754123881186161:ℚ)/2310400000000000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((3320690647:ℚ)/5000000000),((1359361487:ℚ)/2000000000),((-488961487:ℚ)/4120000000),((-173563549:ℚ)/4331250000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((5076980383:ℚ)/10000000000),((36621331270961091890862834438295985579876529089967:ℚ)/853692968750000000000000000000000000000000000000000),((-2180065170381331715731:ℚ)/14440000000000000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((6702026779:ℚ)/10000000000),((1371490971:ℚ)/2000000000),((-501090971:ℚ)/4158000000),((-1102026779:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((4910342781:ℚ)/10000000000),((43048323380646030816701118096856900506269586931061:ℚ)/972504225000000000000000000000000000000000000000000),((-215451400590933120550319:ℚ)/57760000000000000000000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((6762648521:ℚ)/10000000000),((6918078711:ℚ)/10000000000),((-2566078711:ℚ)/20980000000),((-1162648521:ℚ)/26462500000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4738410127:ℚ)/10000000000),((1315963791906688303055641403016142286304301213272185919:ℚ)/28858016225000000000000000000000000000000000000000000000),((-422996707093685544203719:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((6823247189:ℚ)/10000000000),((1395735931:ℚ)/2000000000),((-525335931:ℚ)/4234000000),((-407749063:ℚ)/8900000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((2280288771:ℚ)/5000000000),((2781484210665427571939524289859016777963100662908691:ℚ)/59298347581250000000000000000000000000000000000000000),((-631357433879294636522239:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-5:ℚ)/16),((-1:ℚ)/4),((6883823421:ℚ)/10000000000),((3504485867:ℚ)/5000000000),((-1328485867:ℚ)/10680000000),((-1283823421:ℚ)/26818750000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((2188059841:ℚ)/5000000000),((535962981193955767334596621941963018344352112880291129:ℚ)/11420497800000000000000000000000000000000000000000000000),((-840534767247689647255919:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-5:ℚ)/16),((-1:ℚ)/4),((3457051659:ℚ)/5000000000),((7039258321:ℚ)/10000000000),((-2687258321:ℚ)/21455000000),((-657051659:ℚ)/13468750000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((214056897:ℚ)/500000000),((4404063193627182471319021632133683918610667856261539563:ℚ)/92588454106640625000000000000000000000000000000000000000),((-236357506402604237394779:ℚ)/14440000000000000000000000)⟩
theorem valid7 : Valid source36 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source36 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source36 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((6944377837:ℚ)/10000000000),((3549907657:ℚ)/5000000000),((-1373907657:ℚ)/10775000000),((-1344377837:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((33473233:ℚ)/80000000),((193240125103239296130658021877178805967508799156271057:ℚ)/3909325732421875000000000000000000000000000000000000000),((-1050529868964740661337871:ℚ)/57760000000000000000000000)⟩
theorem valid8 : Valid source36 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source36 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((7004911029:ℚ)/10000000000),((3580175611:ℚ)/5000000000),((-1404175611:ℚ)/10870000000),((-1404911029:ℚ)/27412500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((796717843:ℚ)/2000000000),((12706101447718182767363942645772777939067671370376459:ℚ)/250852637304687500000000000000000000000000000000000000),((-1261343840001330190816319:ℚ)/57760000000000000000000000)⟩
theorem valid9 : Valid source36 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((7065423573:ℚ)/10000000000),((451304163:ℚ)/625000000),((-179304163:ℚ)/1370625000),((-1465423573:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3773047183:ℚ)/10000000000),((9702004453091030628538987622487519956790457423849:ℚ)/187127455902099609375000000000000000000000000000000),((-1472977760494546206707711:ℚ)/57760000000000000000000000)⟩
theorem valid10 : Valid source36 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source36 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((7125916019:ℚ)/10000000000),((7341837973:ℚ)/10000000000),((-2989837973:ℚ)/22120000000),((-508638673:ℚ)/9375000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((110960837:ℚ)/312500000),((267610482659121974918519703510546421352960671992267779:ℚ)/4831782200000000000000000000000000000000000000000000000),((-1685432653344479600851999:ℚ)/57760000000000000000000000)⟩
theorem valid11 : Valid source36 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source36 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((1811710683:ℚ)/2500000000),((373136677:ℚ)/500000000),((-17281853:ℚ)/125000000),((-411710683:ℚ)/7150000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((612094561:ℚ)/2000000000),((351539634733868780889092047247967300696797209853:ℚ)/6103515625000000000000000000000000000000000000000),((-132050581848456339630401:ℚ)/3610000000000000000000000)⟩
theorem valid12 : Valid source36 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((736769521:ℚ)/1000000000),((1986407753:ℚ)/2500000000),((-898407753:ℚ)/5720000000),((-2897861:ℚ)/50000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((1239423643:ℚ)/5000000000),((10686687512596686361674386394838765164869152744563177:ℚ)/146210350000000000000000000000000000000000000000000000),((-25434813570490057754219:ℚ)/577600000000000000000000)⟩
theorem valid13 : Valid source36 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source36 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((3925217203:ℚ)/5000000000),((1685516349:ℚ)/2000000000),((-815116349:ℚ)/4880000000),((-375072401:ℚ)/5400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((7234985797732064235116691315159797125628123778102309:ℚ)/90792400000000000000000000000000000000000000000000000),((-7493221:ℚ)/128000000)⟩
theorem valid14 : Valid source36 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((52076539:ℚ)/62500000),((2587168957:ℚ)/2500000000),((-1499168957:ℚ)/6480000000),((-17076539:ℚ)/250000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((20578745693386679821700812606602896198504123399947111:ℚ)/159432300000000000000000000000000000000000000000000000),((-7493221:ℚ)/128000000)⟩
theorem valid15 : Valid source36 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((10252920859:ℚ)/10000000000),((14173271049:ℚ)/10000000000),((-9821271049:ℚ)/32000000000),((-4652920859:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((4150745979746334387803801451600654247:ℚ)/20480000000000000000000000000000000000),((-7493221:ℚ)/128000000)⟩
theorem valid16 : Valid source36 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((431:ℚ)/640) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source36 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source36 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source36 nn0 nn1 Qcell ((431:ℚ)/640) ((45:ℚ)/64) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source36 nn0 nn1 Qcell ((431:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC12
#check @N11Formalization.C450Source36GroupedC12.bound
#print axioms N11Formalization.C450Source36GroupedC12.valid0
#print axioms N11Formalization.C450Source36GroupedC12.valid1
#print axioms N11Formalization.C450Source36GroupedC12.valid2
#print axioms N11Formalization.C450Source36GroupedC12.valid3
#print axioms N11Formalization.C450Source36GroupedC12.valid4
#print axioms N11Formalization.C450Source36GroupedC12.valid5
#print axioms N11Formalization.C450Source36GroupedC12.valid6
#print axioms N11Formalization.C450Source36GroupedC12.valid7
#print axioms N11Formalization.C450Source36GroupedC12.valid8
#print axioms N11Formalization.C450Source36GroupedC12.valid9
#print axioms N11Formalization.C450Source36GroupedC12.valid10
#print axioms N11Formalization.C450Source36GroupedC12.valid11
#print axioms N11Formalization.C450Source36GroupedC12.valid12
#print axioms N11Formalization.C450Source36GroupedC12.valid13
#print axioms N11Formalization.C450Source36GroupedC12.valid14
#print axioms N11Formalization.C450Source36GroupedC12.valid15
#print axioms N11Formalization.C450Source36GroupedC12.valid16
#print axioms N11Formalization.C450Source36GroupedC12.bound
#print axioms N11Formalization.C450Source36GroupedC12.endpoint_checks
