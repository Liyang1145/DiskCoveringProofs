import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((6918954157:ℚ)/10000000000),((1788279773:ℚ)/2500000000),((-14551077503:ℚ)/24800000000),((-4806954157:ℚ)/10110000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((533217219:ℚ)/1250000000),((56640682541076017983676978475029029:ℚ)/153760000000000000000000000000000000),((7022052267592030991463227539:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((879905859:ℚ)/1250000000),((3606591369:ℚ)/5000000000),((-29432505059:ℚ)/50550000000),((-615905859:ℚ)/1275625000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((3865460459:ℚ)/10000000000),((646463659207884228262105445256837:ℚ)/1774515625000000000000000000000000),((326312259014280646104662873:ℚ)/693120000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((7099371277:ℚ)/10000000000),((909154183:ℚ)/1250000000),((-7440696013:ℚ)/12756250000),((-4987371277:ℚ)/10300000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((3649886863:ℚ)/10000000000),((27344576434247619654543877501623461:ℚ)/75102421875000000000000000000000000),((6930610949149450465358526419:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((1118669:ℚ)/1562500),((7333271631:ℚ)/10000000000),((-60185987941:ℚ)/103000000000),((-450668:ℚ)/928125),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((136858137:ℚ)/400000000),((482587534866415406981499530499663243:ℚ)/1326125000000000000000000000000000000),((168448653665542110271:ℚ)/361000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((1804894559:ℚ)/2500000000),((7393297587:ℚ)/10000000000),((-60846273457:ℚ)/103950000000),((-1276894559:ℚ)/2622500000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((1588690543:ℚ)/5000000000),((23395179546036623311756406221842469:ℚ)/64319062500000000000000000000000000),((429279117060227399288956891:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((14218089:ℚ)/19531250),((7513314203:ℚ)/10000000000),((-62166456233:ℚ)/104900000000),((-3364363:ℚ)/6953125),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((2913735353:ℚ)/10000000000),((504767861879293870181887552250876047:ℚ)/1375501250000000000000000000000000000),((19560922540151713496267:ℚ)/42304687500000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((7399789767:ℚ)/10000000000),((7753214903:ℚ)/10000000000),((-64805363933:ℚ)/106800000000),((-5287789767:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2300431879:ℚ)/10000000000),((14784410087807638301674743040005929:ℚ)/39605000000000000000000000000000000),((20320413845522622897558324737:ℚ)/44359680000000000000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((7639901769:ℚ)/10000000000),((1998238463:ℚ)/2500000000),((-16860623093:ℚ)/27650000000),((-425223213:ℚ)/880000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((71213521904931811296276628027564127:ℚ)/191130625000000000000000000000000000),((461590233:ℚ)/1024000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((3939918783:ℚ)/5000000000),((2237645317:ℚ)/2500000000),((-19494098487:ℚ)/28600000000),((-961306261:ℚ)/2160000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((251128635266262026248828958485089799:ℚ)/613470000000000000000000000000000000),((461590233:ℚ)/1024000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((8838134109:ℚ)/10000000000),((10861451793:ℚ)/10000000000),((-98995969723:ℚ)/129600000000),((-6726134109:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((17456259312932571458221825022782411:ℚ)/38880000000000000000000000000000000),((461590233:ℚ)/1024000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((10749954771:ℚ)/10000000000),((14674168309:ℚ)/10000000000),((-140935851399:ℚ)/160000000000),((-2879318257:ℚ)/7360000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((339138188731330546108548683:ℚ)/640000000000000000000000000),((461590233:ℚ)/1024000000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source34 nn0 nn1 Qcell ((2041:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source34 nn0 nn1 Qcell ((1049:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source34 nn0 nn1 Qcell ((1049:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC06
#check @N11Formalization.C450Source34GroupedC06.bound
#print axioms N11Formalization.C450Source34GroupedC06.valid0
#print axioms N11Formalization.C450Source34GroupedC06.valid1
#print axioms N11Formalization.C450Source34GroupedC06.valid2
#print axioms N11Formalization.C450Source34GroupedC06.valid3
#print axioms N11Formalization.C450Source34GroupedC06.valid4
#print axioms N11Formalization.C450Source34GroupedC06.valid5
#print axioms N11Formalization.C450Source34GroupedC06.valid6
#print axioms N11Formalization.C450Source34GroupedC06.valid7
#print axioms N11Formalization.C450Source34GroupedC06.valid8
#print axioms N11Formalization.C450Source34GroupedC06.valid9
#print axioms N11Formalization.C450Source34GroupedC06.valid10
#print axioms N11Formalization.C450Source34GroupedC06.bound
#print axioms N11Formalization.C450Source34GroupedC06.endpoint_checks
