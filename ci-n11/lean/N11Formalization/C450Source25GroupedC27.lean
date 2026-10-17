import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((2750340889:ℚ)/5000000000),((606125271:ℚ)/1000000000),((3486340889:ℚ)/5340000000),((8203377981:ℚ)/9920000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((761540427:ℚ)/1000000000),((-2057666471257092157008028606655339:ℚ)/12689442000000000000000000000000000),((-847206816570102525016267:ℚ)/2217984000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((2989247843:ℚ)/5000000000),((3150045683:ℚ)/5000000000),((3725247843:ℚ)/5530000000),((42330502513:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3327208373:ℚ)/5000000000),((-195157234364156462638226023145960699414219869488698913:ℚ)/1056952356250000000000000000000000000000000000000000000),((-7016397181500871422464881:ℚ)/18483200000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/8),((11:ℚ)/16),((1243451289:ℚ)/2000000000),((3209738253:ℚ)/5000000000),((1537851289:ℚ)/2250000000),((42987120783:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((245106591:ℚ)/400000000),((-1542362333515728550561323886393444563454222885940011:ℚ)/7910156250000000000000000000000000000000000000000000),((-20980725544094297935092883:ℚ)/55449600000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((6336604643:ℚ)/10000000000),((3269420193:ℚ)/5000000000),((7808604643:ℚ)/11440000000),((4849291347:ℚ)/6250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5849063989:ℚ)/10000000000),((-165605588742505536832740178616710947490106511608919467:ℚ)/850678400000000000000000000000000000000000000000000000),((-1099555653616994556130777:ℚ)/2918400000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((258237313:ℚ)/400000000),((6658184057:ℚ)/10000000000),((317117313:ℚ)/465200000),((88600024627:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5558260947:ℚ)/10000000000),((-30572696112830157668363980643230773559158745194243:ℚ)/157303774700000000000000000000000000000000000000000),((-27733889697182831710932921:ℚ)/73932800000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((6575241981:ℚ)/10000000000),((6777508503:ℚ)/10000000000),((8047241981:ℚ)/11820000000),((89912593533:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5253201809:ℚ)/10000000000),((-500644080193081135784552044931806628535808101209403551:ℚ)/2580313387500000000000000000000000000000000000000000000),((-82829221363638550585575883:ℚ)/221798400000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((3347266519:ℚ)/5000000000),((3448407323:ℚ)/5000000000),((4083266519:ℚ)/6005000000),((45612480553:ℚ)/59100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4931212751:ℚ)/10000000000),((-262128950071967937114758431960942587099938929906104461:ℚ)/1353377813281250000000000000000000000000000000000000000),((-6870740613734090722622241:ℚ)/18483200000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((6813806863:ℚ)/10000000000),((1754025837:ℚ)/2500000000),((8285806863:ℚ)/12200000000),((23134284207:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4588701179:ℚ)/10000000000),((-2194180097013324605119852203067211597980542299294141653:ℚ)/11349050000000000000000000000000000000000000000000000000),((-5128791744990921827341603:ℚ)/13862400000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((6933064267:ℚ)/10000000000),((7135375419:ℚ)/10000000000),((2801688089:ℚ)/4130000000),((93849129609:ℚ)/122000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2110320979:ℚ)/5000000000),((-21241126058405880962477920856578876222859268533003051:ℚ)/110070307812500000000000000000000000000000000000000000),((-81664563795432608729948707:ℚ)/221798400000000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((1763076503:ℚ)/2500000000),((7254631619:ℚ)/10000000000),((2131076503:ℚ)/3145000000),((95160947809:ℚ)/123900000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1909811357:ℚ)/5000000000),((-36569747944104352015433736453079152299608134595157:ℚ)/189863730621337890625000000000000000000000000000000),((-27086858571247513070261969:ℚ)/73932800000000000000000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((3585766407:ℚ)/5000000000),((7493099221:ℚ)/10000000000),((4321766407:ℚ)/6480000000),((97784091431:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((33738733:ℚ)/100000000),((-1283666315641441344880240463224261882859066450532911:ℚ)/6998400000000000000000000000000000000000000000000000),((-26784714412488548206290689:ℚ)/73932800000000000000000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((1481988847:ℚ)/2000000000),((9399177913:ℚ)/10000000000),((1776388847:ℚ)/3200000000),((118750957043:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((448216609:ℚ)/2000000000),((-1202120098344990814883151263032808001954564350785733:ℚ)/12800000000000000000000000000000000000000000000000000),((-3695917426435707:ℚ)/10240000000000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((9315670401:ℚ)/10000000000),((1650787479:ℚ)/1250000000),((10787670401:ℚ)/22080000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-494277723929841344871251:ℚ)/15235200000000000000000000),((-23133897:ℚ)/64000000)⟩
theorem valid12 : Valid source25 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source25 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((1239:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source25 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source25 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC27
#check @N11Formalization.C450Source25GroupedC27.bound
#print axioms N11Formalization.C450Source25GroupedC27.valid0
#print axioms N11Formalization.C450Source25GroupedC27.valid1
#print axioms N11Formalization.C450Source25GroupedC27.valid2
#print axioms N11Formalization.C450Source25GroupedC27.valid3
#print axioms N11Formalization.C450Source25GroupedC27.valid4
#print axioms N11Formalization.C450Source25GroupedC27.valid5
#print axioms N11Formalization.C450Source25GroupedC27.valid6
#print axioms N11Formalization.C450Source25GroupedC27.valid7
#print axioms N11Formalization.C450Source25GroupedC27.valid8
#print axioms N11Formalization.C450Source25GroupedC27.valid9
#print axioms N11Formalization.C450Source25GroupedC27.valid10
#print axioms N11Formalization.C450Source25GroupedC27.valid11
#print axioms N11Formalization.C450Source25GroupedC27.valid12
#print axioms N11Formalization.C450Source25GroupedC27.bound
#print axioms N11Formalization.C450Source25GroupedC27.endpoint_checks
