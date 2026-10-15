import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((340607343:ℚ)/500000000),((7039246877:ℚ)/10000000000),((-5055246877:ℚ)/9920000000),((-2041466087:ℚ)/5055000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2296814973:ℚ)/5000000000),((38764161643278781570326303938499511:ℚ)/123008000000000000000000000000000000),((332021972133571037555447:ℚ)/924160000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((6932522677:ℚ)/10000000000),((3549685641:ℚ)/5000000000),((-2557685641:ℚ)/5055000000),((-3224054161:ℚ)/7850000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((527797653:ℚ)/1250000000),((83019905940196928554619773143229:ℚ)/266177343750000000000000000000000),((130792123543814280349115487:ℚ)/369664000000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((3496343713:ℚ)/5000000000),((1431896321:ℚ)/2000000000),((-1035096321:ℚ)/2041000000),((-21227093417:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((2012424947:ℚ)/5000000000),((374669725561851186120070722923257:ℚ)/1201638750000000000000000000000000),((32443406577176763386395607:ℚ)/92416000000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7052837321:ℚ)/10000000000),((7219578241:ℚ)/10000000000),((-5235578241:ℚ)/10300000000),((-42995535889:ℚ)/103950000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((3817746741:ℚ)/10000000000),((20668678367405989789561697217206777:ℚ)/66306250000000000000000000000000000),((128748349889648066856039623:ℚ)/369664000000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((7112972779:ℚ)/10000000000),((7279661573:ℚ)/10000000000),((-5295661573:ℚ)/10395000000),((-43536755011:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((899853461:ℚ)/2500000000),((1002237875897273754265669640592161:ℚ)/3215953125000000000000000000000000),((127716292313633062154917023:ℚ)/369664000000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7173094203:ℚ)/10000000000),((1467946393:ℚ)/2000000000),((-1071146393:ℚ)/2098000000),((-44077847827:ℚ)/105850000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((3367661403:ℚ)/10000000000),((1714365967994900683496110188639917:ℚ)/5502005000000000000000000000000000),((126677451654249593176072127:ℚ)/369664000000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((7233201979:ℚ)/10000000000),((1849947443:ℚ)/2500000000),((-1353947443:ℚ)/2646250000),((-44618817811:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((3119493251:ℚ)/10000000000),((8181161065939725330623475588491743:ℚ)/26259896484375000000000000000000000),((348010598593712646554343:ℚ)/1024000000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((7293296481:ℚ)/10000000000),((7519868979:ℚ)/10000000000),((-5535868979:ℚ)/10680000000),((-45159668329:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((570123611:ℚ)/2000000000),((14936918469106602404046892456204141:ℚ)/47526000000000000000000000000000000),((124579413838130915365738583:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((7413447087:ℚ)/10000000000),((3819950887:ℚ)/5000000000),((-2827950887:ℚ)/5435000000),((-46241023783:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((17761989:ℚ)/80000000),((4350744194244582942239868162415577:ℚ)/13846511718750000000000000000000000),((122454222497309060866073207:ℚ)/369664000000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((7533548747:ℚ)/10000000000),((7879837571:ℚ)/10000000000),((-5895837571:ℚ)/11060000000),((-47321938723:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1323356147:ℚ)/10000000000),((48857936191132320792239241808365077:ℚ)/152904500000000000000000000000000000),((120301864649497535262066527:ℚ)/369664000000000000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((971701899:ℚ)/1250000000),((4419067057:ℚ)/5000000000),((-3427067057:ℚ)/5720000000),((-6185317091:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((42994491370009020391271044208296981:ℚ)/122694000000000000000000000000000000),((8247849:ℚ)/25600000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((4366177853:ℚ)/5000000000),((1343744347:ℚ)/1250000000),((-1095744347:ℚ)/1620000000),((-29055600677:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((140036058728445569838966329297357:ℚ)/364500000000000000000000000000000),((8247849:ℚ)/25600000)⟩
theorem valid11 : Valid source33 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((133060081:ℚ)/125000000),((14563778553:ℚ)/10000000000),((-12579778553:ℚ)/16000000000),((-941540729:ℚ)/2760000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((14483969465040718374391633:ℚ)/32000000000000000000000000),((8247849:ℚ)/25600000)⟩
theorem valid12 : Valid source33 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source33 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source33 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source33 nn0 nn1 Qcell ((2117:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source33 nn0 nn1 Qcell ((2117:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC07
#check @N11Formalization.C450Source33GroupedC07.bound
#print axioms N11Formalization.C450Source33GroupedC07.valid0
#print axioms N11Formalization.C450Source33GroupedC07.valid1
#print axioms N11Formalization.C450Source33GroupedC07.valid2
#print axioms N11Formalization.C450Source33GroupedC07.valid3
#print axioms N11Formalization.C450Source33GroupedC07.valid4
#print axioms N11Formalization.C450Source33GroupedC07.valid5
#print axioms N11Formalization.C450Source33GroupedC07.valid6
#print axioms N11Formalization.C450Source33GroupedC07.valid7
#print axioms N11Formalization.C450Source33GroupedC07.valid8
#print axioms N11Formalization.C450Source33GroupedC07.valid9
#print axioms N11Formalization.C450Source33GroupedC07.valid10
#print axioms N11Formalization.C450Source33GroupedC07.valid11
#print axioms N11Formalization.C450Source33GroupedC07.valid12
#print axioms N11Formalization.C450Source33GroupedC07.bound
#print axioms N11Formalization.C450Source33GroupedC07.endpoint_checks
