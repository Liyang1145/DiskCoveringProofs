import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((780930047:ℚ)/1250000000),((6546255763:ℚ)/10000000000),((-5558767289:ℚ)/99200000000),((139069953:ℚ)/6200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((757283359:ℚ)/1250000000),((5498900125340361090676639170318121:ℚ)/29791000000000000000000000000000000),((-213420649771813226666389:ℚ)/1155200000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((1297491761:ℚ)/2000000000),((6786045289:ℚ)/10000000000),((-6278135867:ℚ)/103000000000),((174508239:ℚ)/10300000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1369784959:ℚ)/2500000000),((2440607190376399690788560624363202771639217839701869:ℚ)/13338952636718750000000000000000000000000000000000000),((-583237456999773485603541:ℚ)/2957312000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((6727295363:ℚ)/10000000000),((863234899:ℚ)/1250000000),((-829704697:ℚ)/13350000000),((632704637:ℚ)/53400000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1209840277:ℚ)/2500000000),((257811603489513080227914021201956017570073454363630560941:ℚ)/1427562225000000000000000000000000000000000000000000000000),((-42953161389674006469909:ℚ)/204800000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((1711787879:ℚ)/2500000000),((7025675361:ℚ)/10000000000),((-6997026083:ℚ)/108700000000),((128212121:ℚ)/13587500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4488632009:ℚ)/10000000000),((264669386734849576753308277997176341844528562705703433:ℚ)/1469839671707153320312500000000000000000000000000000000),((-998116686516433549391461:ℚ)/4620800000000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((6966969149:ℚ)/10000000000),((7145435741:ℚ)/10000000000),((-7356307223:ℚ)/110600000000),((393030851:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4110382639:ℚ)/10000000000),((1937023854000101530805795235583406260584028906175175369:ℚ)/10785228125000000000000000000000000000000000000000000000),((-16434451497426914628168221:ℚ)/73932800000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((7086750249:ℚ)/10000000000),((227036317:ℚ)/312500000),((-241108951:ℚ)/3515625000),((273249751:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1848066149:ℚ)/5000000000),((99662455111743310080318228856107746967932054054012681101:ℚ)/556182861328125000000000000000000000000000000000000000000),((-50699554817338014042506063:ℚ)/221798400000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((7206492089:ℚ)/10000000000),((3692428131:ℚ)/5000000000),((-4037284393:ℚ)/57200000000),((153507911:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1616020521:ℚ)/5000000000),((78442197731185563071293359372506616320053734219295923487:ℚ)/438631050000000000000000000000000000000000000000000000000),((-17366055805352756569962341:ℚ)/73932800000000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((183153067:ℚ)/250000000),((7504519677:ℚ)/10000000000),((-8433559031:ℚ)/116300000000),((846933:ℚ)/1453750000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2692769279:ℚ)/10000000000),((428515617719912105301042921229963362441401249152327:ℚ)/2400265116882324218750000000000000000000000000000000),((-11145488756490430036269:ℚ)/46208000000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((1489144931:ℚ)/2000000000),((3871880109:ℚ)/5000000000),((-4575640327:ℚ)/59100000000),((-17144931:ℚ)/12200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1009168947:ℚ)/5000000000),((601122181848830689920272164698536741545281364579254350129:ℚ)/3353644275000000000000000000000000000000000000000000000000),((-2027739715258278958421:ℚ)/8192000000000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((7684848181:ℚ)/10000000000),((513870753:ℚ)/625000000),((-661612259:ℚ)/7625000000),((-108282727:ℚ)/21600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((115736675189243991292191477189900431326972594834515312949:ℚ)/640353600000000000000000000000000000000000000000000000000),((-4091257:ℚ)/16000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((4081403481:ℚ)/5000000000),((10131584109:ℚ)/10000000000),((-16314752327:ℚ)/129600000000),((-401403481:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3094891713840386078985551957713671945476894192762846343869:ℚ)/16200000000000000000000000000000000000000000000000000000000),((-4091257:ℚ)/16000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((5035906041:ℚ)/5000000000),((1742859959:ℚ)/1250000000),((-3468579877:ℚ)/20000000000),((-1355906041:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((84769445007005047857649111461919379714945656749756749167:ℚ)/394210800000000000000000000000000000000000000000000000000),((-4091257:ℚ)/16000000)⟩
theorem valid11 : Valid source24 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC14
#check @N11Formalization.C450Source24GroupedC14.bound
#print axioms N11Formalization.C450Source24GroupedC14.valid0
#print axioms N11Formalization.C450Source24GroupedC14.valid1
#print axioms N11Formalization.C450Source24GroupedC14.valid2
#print axioms N11Formalization.C450Source24GroupedC14.valid3
#print axioms N11Formalization.C450Source24GroupedC14.valid4
#print axioms N11Formalization.C450Source24GroupedC14.valid5
#print axioms N11Formalization.C450Source24GroupedC14.valid6
#print axioms N11Formalization.C450Source24GroupedC14.valid7
#print axioms N11Formalization.C450Source24GroupedC14.valid8
#print axioms N11Formalization.C450Source24GroupedC14.valid9
#print axioms N11Formalization.C450Source24GroupedC14.valid10
#print axioms N11Formalization.C450Source24GroupedC14.valid11
#print axioms N11Formalization.C450Source24GroupedC14.bound
#print axioms N11Formalization.C450Source24GroupedC14.endpoint_checks
