import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((6641410249:ℚ)/10000000000),((6860755709:ℚ)/10000000000),((-4380755709:ℚ)/12400000000),((-26009871743:ℚ)/101100000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((5076902017:ℚ)/10000000000),((341929004509134899176366510629367881:ℚ)/1489550000000000000000000000000000000),((2665768032239876088139880761:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((1690522661:ℚ)/2500000000),((872667631:ℚ)/1250000000),((-187555877:ℚ)/526562500),((-6713658627:ℚ)/25750000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((2370009273:ℚ)/5000000000),((1311963745770743822235603053559286503920904556361:ℚ)/5703084617853164672851562500000000000000000000000),((159991261872390715208698881:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((6882698141:ℚ)/10000000000),((1408321597:ℚ)/2000000000),((-912321597:ℚ)/2575000000),((-9232962329:ℚ)/34650000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((2189806133:ℚ)/5000000000),((9492689141678392490985485722095747486575928962589:ℚ)/41684226989746093750000000000000000000000000000000),((2452785890414661326654883441:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((43393599:ℚ)/62500000),((7101858409:ℚ)/10000000000),((-660265487:ℚ)/1856250000),((-175755193:ℚ)/655625000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((2094345993:ℚ)/5000000000),((27621383025720555120109520827261555650586977196327:ℚ)/121136627197265625000000000000000000000000000000000),((93703549230352733619561:ℚ)/577600000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((3501618411:ℚ)/5000000000),((895261597:ℚ)/1250000000),((-585261597:ℚ)/1639062500),((-14271328877:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((997316087:ℚ)/2500000000),((628334434789229198689122227616871217179401220767849:ℚ)/2752114889621734619140625000000000000000000000000000),((586135919413195072229782881:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((7063481549:ℚ)/10000000000),((7222311527:ℚ)/10000000000),((-4742311527:ℚ)/13231250000),((-9654790281:ℚ)/35600000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((1889988509:ℚ)/5000000000),((82737680383155384872638103390728734029262783999481071:ℚ)/361928390998840332031250000000000000000000000000000000),((2289984178463897208524302161:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((7123710467:ℚ)/10000000000),((3641257543:ℚ)/5000000000),((-800419181:ℚ)/2225000000),((-29385973269:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3559084757:ℚ)/10000000000),((4727488877638845449146707769745812145979241872920711:ℚ)/20653388671875000000000000000000000000000000000000000),((2235132203841858653398407729:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((897990501:ℚ)/1250000000),((1468540773:ℚ)/2000000000),((-972540773:ℚ)/2693750000),((-3725933507:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((207766773:ℚ)/625000000),((2799959739294994507781507957389157043400111957375021:ℚ)/12216642913818359375000000000000000000000000000000000),((34062306228195530237509761:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((3622061293:ℚ)/5000000000),((93287983:ℚ)/125000000),((-62287983:ℚ)/169843750),((-15114429051:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3072329867:ℚ)/10000000000),((22211026555176371620704516351468301980511704333:ℚ)/95692686960101127624511718750000000000000000000),((531137553833028803121619089:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((3682238217:ℚ)/5000000000),((770354727:ℚ)/1000000000),((-522354727:ℚ)/1382500000),((-15535667519:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((312006319:ℚ)/1250000000),((56086124945157736372591274501372164571847990276977:ℚ)/235926865234375000000000000000000000000000000000000),((503199138147922326231948729:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((1901255309:ℚ)/2500000000),((8663789631:ℚ)/10000000000),((-6183789631:ℚ)/14300000000),((-2729595721:ℚ)/10800000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((365664202865981658432443771596903496874776231477256901:ℚ)/1370722031250000000000000000000000000000000000000000000),((123999931:ℚ)/1024000000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((8565386401:ℚ)/10000000000),((1057837009:ℚ)/1000000000),((-809837009:ℚ)/1620000000),((-39477704807:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((148041753377819079254628399138987425677218132437171:ℚ)/498225937500000000000000000000000000000000000000000),((123999931:ℚ)/1024000000)⟩
theorem valid11 : Valid source33 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((10480140877:ℚ)/10000000000),((3598851553:ℚ)/2500000000),((-2978851553:ℚ)/5000000000),((-52880986139:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((5591075322344888416811587320902367:ℚ)/15625000000000000000000000000000000),((123999931:ℚ)/1024000000)⟩
theorem valid12 : Valid source33 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source33 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2079:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source33 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source33 nn0 nn1 Qcell ((2079:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source33 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
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
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC09
#check @N11Formalization.C450Source33GroupedC09.bound
#print axioms N11Formalization.C450Source33GroupedC09.valid0
#print axioms N11Formalization.C450Source33GroupedC09.valid1
#print axioms N11Formalization.C450Source33GroupedC09.valid2
#print axioms N11Formalization.C450Source33GroupedC09.valid3
#print axioms N11Formalization.C450Source33GroupedC09.valid4
#print axioms N11Formalization.C450Source33GroupedC09.valid5
#print axioms N11Formalization.C450Source33GroupedC09.valid6
#print axioms N11Formalization.C450Source33GroupedC09.valid7
#print axioms N11Formalization.C450Source33GroupedC09.valid8
#print axioms N11Formalization.C450Source33GroupedC09.valid9
#print axioms N11Formalization.C450Source33GroupedC09.valid10
#print axioms N11Formalization.C450Source33GroupedC09.valid11
#print axioms N11Formalization.C450Source33GroupedC09.valid12
#print axioms N11Formalization.C450Source33GroupedC09.bound
#print axioms N11Formalization.C450Source33GroupedC09.endpoint_checks
