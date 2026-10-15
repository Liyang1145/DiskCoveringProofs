import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/8),((-1:ℚ)/16),((6168401427:ℚ)/10000000000),((3241347479:ℚ)/5000000000),((1078652521:ℚ)/25750000000),((11751598573:ℚ)/99200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((779820371:ℚ)/1250000000),((12208299527153763266550552511269633669317486573979518897:ℚ)/320134863281250000000000000000000000000000000000000000000),((-8572745737624891726124334997:ℚ)/44359680000000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((3204854343:ℚ)/5000000000),((6603093931:ℚ)/10000000000),((2036906069:ℚ)/52450000000),((5755145657:ℚ)/51500000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1418120609:ℚ)/2500000000),((8783681411272949320993292076769310734671878684377841759:ℚ)/225453251757812500000000000000000000000000000000000000000),((-2277844329597692115957501757:ℚ)/11089920000000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((6530256499:ℚ)/10000000000),((840429131:ℚ)/1250000000),((239570869:ℚ)/6675000000),((11389743501:ℚ)/104900000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((5370057691:ℚ)/10000000000),((18662041069955089038004927228034233085529617738065511:ℚ)/464701245117187500000000000000000000000000000000000000),((-3127125358810203212080604231:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((3325369469:ℚ)/5000000000),((6843715533:ℚ)/10000000000),((1796284467:ℚ)/54350000000),((1878210177:ℚ)/17800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2525798197:ℚ)/5000000000),((41458839745557430236738322859332828051271301655602964377:ℚ)/1003410549218750000000000000000000000000000000000000000000),((-804320027683740401166069991:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((6771159529:ℚ)/10000000000),((870493047:ℚ)/1250000000),((209506953:ℚ)/6912500000),((11148840471:ℚ)/108700000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4713809099:ℚ)/10000000000),((1368903944622762081823402402316654630857438687660827:ℚ)/32255626106262207031250000000000000000000000000000000),((-3307592344020523862390162271:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((6891521547:ℚ)/10000000000),((3542061181:ℚ)/5000000000),((777938819:ℚ)/28125000000),((11028478453:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((217607817:ℚ)/500000000),((70922919657311244190718320259185978002077331563678323:ℚ)/1629441976547241210937500000000000000000000000000000000),((-10194192627787981816521172837:ℚ)/44359680000000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((7011828039:ℚ)/10000000000),((1440850417:ℚ)/2000000000),((287149583:ℚ)/11440000000),((10908171961:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((990015181:ℚ)/2500000000),((417159550822561407572159737819288687233036752057264173:ℚ)/9357462400000000000000000000000000000000000000000000000),((-28991947706920357505198773:ℚ)/122880000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((1783020461:ℚ)/2500000000),((3722188129:ℚ)/5000000000),((597811871:ℚ)/29550000000),((2696979539:ℚ)/28600000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((88183427:ℚ)/250000000),((69929058521454989985344824668864022416930960666182207:ℚ)/1493236914062500000000000000000000000000000000000000000),((-223718418929805756304729351:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((3686220899:ℚ)/5000000000),((768433441:ℚ)/1000000000),((95566559:ℚ)/6100000000),((1757926367:ℚ)/19700000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2453262833:ℚ)/10000000000),((207312173039247683967333518109468070885596397295631343:ℚ)/4255893750000000000000000000000000000000000000000000000),((-940396504520284897416811431:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((7612620563:ℚ)/10000000000),((8163812181:ℚ)/10000000000),((158729273:ℚ)/21600000000),((10307379437:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1102798630092449816429323476430919632622460049553788561:ℚ)/20995200000000000000000000000000000000000000000000000000),((-272488013:ℚ)/1024000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((1011562451:ℚ)/1250000000),((403122729:ℚ)/400000000),((-19174243:ℚ)/864000000),((45497687:ℚ)/600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((50377931944154586889763959783814293605854444440621:ℚ)/755827200000000000000000000000000000000000000000000),((-272488013:ℚ)/1024000000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((2501832153:ℚ)/2500000000),((2779037623:ℚ)/2000000000),((-1051037623:ℚ)/16000000000),((1978167847:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((95404757922263063054094352420279961:ℚ)/1024000000000000000000000000000000000),((-272488013:ℚ)/1024000000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC15
#check @N11Formalization.C450Source29GroupedC15.bound
#print axioms N11Formalization.C450Source29GroupedC15.valid0
#print axioms N11Formalization.C450Source29GroupedC15.valid1
#print axioms N11Formalization.C450Source29GroupedC15.valid2
#print axioms N11Formalization.C450Source29GroupedC15.valid3
#print axioms N11Formalization.C450Source29GroupedC15.valid4
#print axioms N11Formalization.C450Source29GroupedC15.valid5
#print axioms N11Formalization.C450Source29GroupedC15.valid6
#print axioms N11Formalization.C450Source29GroupedC15.valid7
#print axioms N11Formalization.C450Source29GroupedC15.valid8
#print axioms N11Formalization.C450Source29GroupedC15.valid9
#print axioms N11Formalization.C450Source29GroupedC15.valid10
#print axioms N11Formalization.C450Source29GroupedC15.valid11
#print axioms N11Formalization.C450Source29GroupedC15.bound
#print axioms N11Formalization.C450Source29GroupedC15.endpoint_checks
