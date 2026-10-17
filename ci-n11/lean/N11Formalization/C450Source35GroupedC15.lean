import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/8),((-1:ℚ)/16),((1533649273:ℚ)/2500000000),((6467874843:ℚ)/10000000000),((4092125157:ℚ)/51500000000),((3906350727:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3157153199:ℚ)/5000000000),((-75065399543453791256543188546445756831112475397238621277917:ℚ)/820398942968750000000000000000000000000000000000000000000000),((-8785332376609718858196679:ℚ)/57760000000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((3188888057:ℚ)/5000000000),((1647278469:ℚ)/2500000000),((992721531:ℚ)/13112500000),((7691111943:ℚ)/51500000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((718775823:ℚ)/1250000000),((-3294872600019730710148239831681574646106803279939221478139:ℚ)/37372399185916137695312500000000000000000000000000000000000),((-37773144656526787585795399:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((6499206033:ℚ)/10000000000),((132993977:ℚ)/200000000),((78206023:ℚ)/1058500000),((15260793967:ℚ)/104900000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((2724697163:ℚ)/5000000000),((-705986276343398550645082775067343273654055455742290159543:ℚ)/8156495122094385156250000000000000000000000000000000000000),((-156372648329002914308481239:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((3279941857:ℚ)/5000000000),((6710261647:ℚ)/10000000000),((3849738353:ℚ)/53400000000),((7600058143:ℚ)/52925000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((264667961:ℚ)/500000000),((-137879988171079613419039198423398519520639542666738202705321:ℚ)/1623006068137500000000000000000000000000000000000000000000000),((-39754222344621378666188599:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/8),((-1:ℚ)/16),((3310268733:ℚ)/5000000000),((6770802879:ℚ)/10000000000),((3789197121:ℚ)/53875000000),((7569731267:ℚ)/53400000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((5133110433:ℚ)/10000000000),((-2521762220364677157890508926986536024298211619022178561169:ℚ)/30240008912611007690429687500000000000000000000000000000000),((-40415992130881932403579439:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((6681167949:ℚ)/10000000000),((1707830783:ℚ)/2500000000),((932169217:ℚ)/13587500000),((15078832051:ℚ)/107750000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4968234607:ℚ)/10000000000),((-238433580909376203212945883830891030816793363806951478134857:ℚ)/2912414797397253417968750000000000000000000000000000000000000),((-164313910039139163146903951:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((3370887899:ℚ)/5000000000),((1722955743:ℚ)/2500000000),((305681419:ℚ)/4568750000),((7509112101:ℚ)/54350000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((959649817:ℚ)/2000000000),((-14152282403335583516750222789645227717416284435404971203899:ℚ)/176064297047034835815429687500000000000000000000000000000000),((-41741684318959450970531551:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((6802361627:ℚ)/10000000000),((3476151473:ℚ)/5000000000),((1803848527:ℚ)/27650000000),((14957638373:ℚ)/109650000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((924516883:ℚ)/2000000000),((-87069013908061823983214191528310530565502826686381289100503:ℚ)/1103113511793176269531250000000000000000000000000000000000000),((-469868345781074011439239:ℚ)/2560000000000000000000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((3431463013:ℚ)/5000000000),((350638179:ℚ)/500000000),((177361821:ℚ)/2788750000),((7448536987:ℚ)/55300000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((4440560771:ℚ)/10000000000),((-28689180597788655522491283317342500246468566504538734387:ℚ)/370118682163709259033203125000000000000000000000000000000),((-43070284597513041665460319:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid source35 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((1730867391:ℚ)/2500000000),((3536602691:ℚ)/5000000000),((1743397309:ℚ)/28125000000),((3709132609:ℚ)/27887500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4251355433:ℚ)/10000000000),((-68604111888505934744781702319490257957583642974448121810487:ℚ)/901146771758794784545898437500000000000000000000000000000000),((-10933922180685762384842231:ℚ)/57760000000000000000000000)⟩
theorem valid9 : Valid source35 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source35 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source35 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((6983992791:ℚ)/10000000000),((7194034431:ℚ)/10000000000),((3365965569:ℚ)/57200000000),((14776007209:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4053956803:ℚ)/10000000000),((-2319093426008450515332886465799434209318469883941345860907:ℚ)/31581435600000000000000000000000000000000000000000000000000),((-177607342565248132751245031:ℚ)/924160000000000000000000000)⟩
theorem valid10 : Valid source35 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((7104980411:ℚ)/10000000000),((1487097401:ℚ)/2000000000),((624902599:ℚ)/11820000000),((14655019589:ℚ)/114400000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((72583071:ℚ)/200000000),((-400973085460566969192585150894987356782252762605811949191:ℚ)/5862758717887500000000000000000000000000000000000000000000),((-182945508621927783640218271:ℚ)/924160000000000000000000000)⟩
theorem valid11 : Valid source35 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((1836683509:ℚ)/2500000000),((7676687563:ℚ)/10000000000),((47267417:ℚ)/1000000000),((1201105497:ℚ)/9850000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2588869187:ℚ)/10000000000),((-15480315031594933268297013091981036257889761817995996953:ℚ)/242556250000000000000000000000000000000000000000000000000),((-12103644265854222849818431:ℚ)/57760000000000000000000000)⟩
theorem valid12 : Valid source35 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source35 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((303528639:ℚ)/400000000),((4079211931:ℚ)/5000000000),((1200788069:ℚ)/32400000000),((566871361:ℚ)/4880000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((55694353:ℚ)/1000000000),((-1630486158876788506361997923183443838066943685158607838183:ℚ)/29296177200000000000000000000000000000000000000000000000000),((-327072970699947463671671:ℚ)/1478656000000000000000000)⟩
theorem valid13 : Valid source35 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((8070463353:ℚ)/10000000000),((10078870337:ℚ)/10000000000),((481129663:ℚ)/80000000000),((13689536647:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-75132845396062286514438822377073000401545183562624412589207:ℚ)/2332800000000000000000000000000000000000000000000000000000000),((-14193031:ℚ)/64000000)⟩
theorem valid14 : Valid source35 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((9992453:ℚ)/10000000),((13903874183:ℚ)/10000000000),((-3343874183:ℚ)/80000000000),((11767547:ℚ)/160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((691336954140462068699293256862845549:ℚ)/128000000000000000000000000000000000000),((-14193031:ℚ)/64000000)⟩
theorem valid15 : Valid source35 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC15
#check @N11Formalization.C450Source35GroupedC15.bound
#print axioms N11Formalization.C450Source35GroupedC15.valid0
#print axioms N11Formalization.C450Source35GroupedC15.valid1
#print axioms N11Formalization.C450Source35GroupedC15.valid2
#print axioms N11Formalization.C450Source35GroupedC15.valid3
#print axioms N11Formalization.C450Source35GroupedC15.valid4
#print axioms N11Formalization.C450Source35GroupedC15.valid5
#print axioms N11Formalization.C450Source35GroupedC15.valid6
#print axioms N11Formalization.C450Source35GroupedC15.valid7
#print axioms N11Formalization.C450Source35GroupedC15.valid8
#print axioms N11Formalization.C450Source35GroupedC15.valid9
#print axioms N11Formalization.C450Source35GroupedC15.valid10
#print axioms N11Formalization.C450Source35GroupedC15.valid11
#print axioms N11Formalization.C450Source35GroupedC15.valid12
#print axioms N11Formalization.C450Source35GroupedC15.valid13
#print axioms N11Formalization.C450Source35GroupedC15.valid14
#print axioms N11Formalization.C450Source35GroupedC15.valid15
#print axioms N11Formalization.C450Source35GroupedC15.bound
#print axioms N11Formalization.C450Source35GroupedC15.endpoint_checks
