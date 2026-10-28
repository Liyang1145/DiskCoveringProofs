import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((5968627771:ℚ)/10000000000),((50701207:ℚ)/78125000),((58837649939:ℚ)/106800000000),((55201207:ℚ)/77500000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3337709361:ℚ)/5000000000),((-1696707381182828281347760963224290587:ℚ)/304546608000000000000000000000000000000),((-58937008699817478242755379:ℚ)/369664000000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((6444081643:ℚ)/10000000000),((840929357:ℚ)/1250000000),((63116734787:ℚ)/110600000000),((912929357:ℚ)/1335000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5587744323:ℚ)/10000000000),((-28035112235566448600348359800437582243385594316726826813:ℚ)/3623836650000000000000000000000000000000000000000000000000),((-59286595479379801193744531:ℚ)/369664000000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((9:ℚ)/16),((5:ℚ)/8),((3340892579:ℚ)/5000000000),((6846270461:ℚ)/10000000000),((32628033211:ℚ)/56250000000),((7422270461:ℚ)/11060000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2483265243:ℚ)/5000000000),((-3233997310579250667639368277598953459684724630044357587:ℚ)/370788574218750000000000000000000000000000000000000000000),((-14865979417389126236768579:ℚ)/92416000000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((6800631753:ℚ)/10000000000),((6965103221:ℚ)/10000000000),((5101975829:ℚ)/8800000000),((7541103221:ℚ)/11250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((925537123:ℚ)/2000000000),((-3404309608111468160240086812183609014385476805846549:ℚ)/387200000000000000000000000000000000000000000000000000),((-164967344432517522106211:ℚ)/1024000000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((108116799:ℚ)/156250000),((7024518577:ℚ)/10000000000),((1053051191:ℚ)/1802343750),((7600518577:ℚ)/11440000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((133252521:ℚ)/312500000),((-126916669630854561535056337883724274682337945717421:ℚ)/13722213107720017433166503906250000000000000000000000),((-14561261438563841386619:ℚ)/90250000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((872361959:ℚ)/1250000000),((7083933273:ℚ)/10000000000),((8491257631:ℚ)/14537500000),((2553311091:ℚ)/3845000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2035464459:ℚ)/5000000000),((-7123583483880808395484995991099797411716977213333989:ℚ)/768084837402343750000000000000000000000000000000000000),((-932624106648376471250939:ℚ)/5776000000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((9:ℚ)/16),((5:ℚ)/8),((879789433:ℚ)/1250000000),((3571673663:ℚ)/5000000000),((8558104897:ℚ)/14656250000),((3859673663:ℚ)/5815000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((967177499:ℚ)/2500000000),((-19603173103875053746459196000728109932783570159053607:ℚ)/2108200120925903320312500000000000000000000000000000000),((-2585399250829924496131:ℚ)/16000000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((7097734529:ℚ)/10000000000),((28811043:ℚ)/40000000),((68999610761:ℚ)/118200000000),((31115043:ℚ)/46900000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((22849473:ℚ)/62500000),((-8017216766898617281898793509067131923208220754671853417:ℚ)/860104462500000000000000000000000000000000000000000000000),((-59778291258363912275799979:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((1431430577:ℚ)/2000000000),((181554339:ℚ)/250000000),((13906875193:ℚ)/23830000000),((65318113:ℚ)/98500000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3430574437:ℚ)/10000000000),((-2370492229185658793402642551829308130106200759750283649:ℚ)/253730922881250000000000000000000000000000000000000000000),((-2392944949476812982440651:ℚ)/14786560000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((7216570549:ℚ)/10000000000),((1830396443:ℚ)/2500000000),((70069134941:ℚ)/120100000000),((1974396443:ℚ)/2978750000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3190024029:ℚ)/10000000000),((-6335542117789217958091070507625487323671477113798690479:ℚ)/676688906640625000000000000000000000000000000000000000000),((-59869061736062970490081619:ℚ)/369664000000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((9:ℚ)/16),((5:ℚ)/8),((7275987537:ℚ)/10000000000),((36904987:ℚ)/50000000),((70603887833:ℚ)/121050000000),((39784987:ℚ)/60050000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((293051677:ℚ)/1000000000),((-3851889074696584117906184788342260413653428531755080609:ℚ)/410592142968750000000000000000000000000000000000000000000),((-59914605264365018342736011:ℚ)/369664000000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((1467080773:ℚ)/2000000000),((930051057:ℚ)/1250000000),((14227726957:ℚ)/24400000000),((334017019:ℚ)/504375000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2646476717:ℚ)/10000000000),((-853339245429404991025330831168902220619185115426401327:ℚ)/90792400000000000000000000000000000000000000000000000000),((-2398410173220556134208051:ℚ)/14786560000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((7394819549:ℚ)/10000000000),((7559228909:ℚ)/10000000000),((71673375941:ℚ)/123900000000),((8135228909:ℚ)/12200000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((232893911:ℚ)/1000000000),((-1280910088561704824139779249914794652007241858804630419:ℚ)/141518967187500000000000000000000000000000000000000000000),((-60006008943311324509719619:ℚ)/369664000000000000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((1878412261:ℚ)/2500000000),((7678047231:ℚ)/10000000000),((18185710349:ℚ)/31450000000),((2751349077:ℚ)/4130000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((301775401:ℚ)/2000000000),((-1725242051155216678217223598024651542652665059958599:ℚ)/189863730621337890625000000000000000000000000000000000),((-3756114677547323789325299:ℚ)/23104000000000000000000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((1526495227:ℚ)/2000000000),((3957838931:ℚ)/5000000000),((14762457043:ℚ)/25920000000),((4245838931:ℚ)/6290000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-34015822285201024069757810457600558290360013550596611:ℚ)/4031078400000000000000000000000000000000000000000000000),((-20832697:ℚ)/128000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((787012353:ℚ)/1000000000),((981649939:ℚ)/1000000000),((7595111177:ℚ)/16000000000),((1039249939:ℚ)/1296000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-761246802019837206583485129332129:ℚ)/480000000000000000000000000000000000),((-20832697:ℚ)/128000000)⟩
theorem valid15 : Valid tenth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((2442762617:ℚ)/2500000000),((6808731769:ℚ)/5000000000),((23264863553:ℚ)/55200000000),((7096731769:ℚ)/8000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2880025563129097554461207:ℚ)/761760000000000000000000000),((-20832697:ℚ)/128000000)⟩
theorem valid16 : Valid tenth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound tenth nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC26
#check @N11Formalization.C450TenthGroupedC26.bound
#print axioms N11Formalization.C450TenthGroupedC26.valid0
#print axioms N11Formalization.C450TenthGroupedC26.valid1
#print axioms N11Formalization.C450TenthGroupedC26.valid2
#print axioms N11Formalization.C450TenthGroupedC26.valid3
#print axioms N11Formalization.C450TenthGroupedC26.valid4
#print axioms N11Formalization.C450TenthGroupedC26.valid5
#print axioms N11Formalization.C450TenthGroupedC26.valid6
#print axioms N11Formalization.C450TenthGroupedC26.valid7
#print axioms N11Formalization.C450TenthGroupedC26.valid8
#print axioms N11Formalization.C450TenthGroupedC26.valid9
#print axioms N11Formalization.C450TenthGroupedC26.valid10
#print axioms N11Formalization.C450TenthGroupedC26.valid11
#print axioms N11Formalization.C450TenthGroupedC26.valid12
#print axioms N11Formalization.C450TenthGroupedC26.valid13
#print axioms N11Formalization.C450TenthGroupedC26.valid14
#print axioms N11Formalization.C450TenthGroupedC26.valid15
#print axioms N11Formalization.C450TenthGroupedC26.valid16
#print axioms N11Formalization.C450TenthGroupedC26.bound
#print axioms N11Formalization.C450TenthGroupedC26.endpoint_checks
