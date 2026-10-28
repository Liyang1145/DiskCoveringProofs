import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((6248216351:ℚ)/10000000000),((6544203029:ℚ)/10000000000),((-6192609087:ℚ)/99200000000),((791783649:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3028236811:ℚ)/5000000000),((1256517888378686144958659213710442109:ℚ)/7626496000000000000000000000000000000),((-37696191995406669207695713:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((6488017421:ℚ)/10000000000),((678379521:ℚ)/1000000000),((-691138563:ℚ)/10300000000),((551982579:ℚ)/51500000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((2738864317:ℚ)/5000000000),((136144692044531077522387852603886509170656908964849013:ℚ)/833684539794921875000000000000000000000000000000000000),((-40334838250091517934188233:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((6727652527:ℚ)/10000000000),((6903535753:ℚ)/10000000000),((-2423535753:ℚ)/35600000000),((312347473:ℚ)/53400000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((241917547:ℚ)/500000000),((38359572353008877101096070978133911754661962108352206511:ℚ)/237927037500000000000000000000000000000000000000000000000),((-42982164568593596463469377:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((3423706689:ℚ)/5000000000),((7023241851:ℚ)/10000000000),((-7629725553:ℚ)/108700000000),((96293311:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4487837931:ℚ)/10000000000),((315014881408027290441429659440068842076430783123697977:ℚ)/1959786228942871093750000000000000000000000000000000000),((-33231852986939740576236419:ℚ)/173280000000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((870884447:ℚ)/1250000000),((1785728819:ℚ)/2500000000),((-285312351:ℚ)/3950000000),((9115553:ℚ)/6912500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((513754019:ℚ)/1250000000),((11819114068919649088360851248848628897582263860858897:ℚ)/73727145385742187500000000000000000000000000000000000),((-713088076510801758123417:ℚ)/3610000000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((885835411:ℚ)/1250000000),((7262557681:ℚ)/10000000000),((-927519227:ℚ)/12500000000),((-5835411:ℚ)/7150000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3696376181:ℚ)/10000000000),((8303836741166107845376946954561522659163627111329993:ℚ)/51921289062500000000000000000000000000000000000000000),((-733877322323664911391073:ℚ)/3610000000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((7206262209:ℚ)/10000000000),((7382170609:ℚ)/10000000000),((-669731679:ℚ)/8800000000),((-166262209:ℚ)/58150000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3232993261:ℚ)/10000000000),((539388111305934994690300937663638820203126372685285854083:ℚ)/3379573284570312500000000000000000000000000000000000000000),((-144902866828329507096325859:ℚ)/693120000000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((1831453443:ℚ)/2500000000),((7501755501:ℚ)/10000000000),((-9065266503:ℚ)/116300000000),((-71453443:ℚ)/14775000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((336787087:ℚ)/1250000000),((8645985483158144394074578628183475546121510973274395259:ℚ)/54269829095458984375000000000000000000000000000000000000),((-9306763494164067572366411:ℚ)/43320000000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((465333707:ℚ)/625000000),((774084649:ℚ)/1000000000),((-326084649:ℚ)/3940000000),((-25333707:ℚ)/3812500000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((505216397:ℚ)/2500000000),((2727422630614605890396167403194913766281948139431636463:ℚ)/17057516860961914062500000000000000000000000000000000000),((-199115276816857608618437:ℚ)/902500000000000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((7684317249:ℚ)/10000000000),((328749841:ℚ)/400000000),((-448649523:ℚ)/4880000000),((-644317249:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((464239868966497506550258178206501246428239414069043623333:ℚ)/2881591200000000000000000000000000000000000000000000000000),((-14600547:ℚ)/64000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((204050273:ℚ)/250000000),((10127571207:ℚ)/10000000000),((-5647571207:ℚ)/43200000000),((-28050273:ℚ)/2000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((57282273149630186026123305510119100557545842815954867:ℚ)/337500000000000000000000000000000000000000000000000000),((-14600547:ℚ)/64000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((10070210733:ℚ)/10000000000),((13937901839:ℚ)/10000000000),((-28373705517:ℚ)/160000000000),((-3030210733:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((100066252963136204345789299824710706814931773340484779861:ℚ)/525614400000000000000000000000000000000000000000000000000),((-14600547:ℚ)/64000000)⟩
theorem valid11 : Valid source23 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC14
#check @N11Formalization.C450Source23GroupedC14.bound
#print axioms N11Formalization.C450Source23GroupedC14.valid0
#print axioms N11Formalization.C450Source23GroupedC14.valid1
#print axioms N11Formalization.C450Source23GroupedC14.valid2
#print axioms N11Formalization.C450Source23GroupedC14.valid3
#print axioms N11Formalization.C450Source23GroupedC14.valid4
#print axioms N11Formalization.C450Source23GroupedC14.valid5
#print axioms N11Formalization.C450Source23GroupedC14.valid6
#print axioms N11Formalization.C450Source23GroupedC14.valid7
#print axioms N11Formalization.C450Source23GroupedC14.valid8
#print axioms N11Formalization.C450Source23GroupedC14.valid9
#print axioms N11Formalization.C450Source23GroupedC14.valid10
#print axioms N11Formalization.C450Source23GroupedC14.valid11
#print axioms N11Formalization.C450Source23GroupedC14.bound
#print axioms N11Formalization.C450Source23GroupedC14.endpoint_checks
