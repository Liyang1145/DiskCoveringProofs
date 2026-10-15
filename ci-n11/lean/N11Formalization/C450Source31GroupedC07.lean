import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((1694467471:ℚ)/2500000000),((1749732009:ℚ)/2500000000),((-1285732009:ℚ)/2480000000),((-3483402413:ℚ)/8425000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4694328823:ℚ)/10000000000),((331426187095453117166359249:ℚ)/1100199687500000000000000000),((7878817547378360437812363:ℚ)/23104000000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((689803903:ℚ)/1000000000),((352948009:ℚ)/500000000),((-86716003:ℚ)/168500000),((-4288235127:ℚ)/10205000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((4331771233:ℚ)/10000000000),((13080955597214281738910322020157298279:ℚ)/43869828031250000000000000000000000000),((1241303899768277866065387:ℚ)/3696640000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((6958103439:ℚ)/10000000000),((7118980003:ℚ)/10000000000),((-5262980003:ℚ)/10205000000),((-43422930951:ℚ)/103000000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((4042462:ℚ)/9765625),((6454478141059850511296042111138351482639:ℚ)/21652969000000000000000000000000000000000),((123155444085265303198136203:ℚ)/369664000000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7018154913:ℚ)/10000000000),((1794746963:ℚ)/2500000000),((-1330746963:ℚ)/2575000000),((-14654464739:ℚ)/34650000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((3938423061:ℚ)/10000000000),((3838867341031073490695593193427636091:ℚ)/12881678906250000000000000000000000000),((122174095457643439916356267:ℚ)/369664000000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((7078193813:ℚ)/10000000000),((7238984057:ℚ)/10000000000),((-163120729:ℚ)/315000000),((-44503744317:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3727172893:ℚ)/10000000000),((1032750267640561263616973866919824764319:ℚ)/3466263150000000000000000000000000000000),((121186342407595166834816467:ℚ)/369664000000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((713822049:ℚ)/1000000000),((364948447:ℚ)/500000000),((-272148447:ℚ)/524500000),((-4504398441:ℚ)/10585000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((175194087:ℚ)/500000000),((2398042640667406706903331084852811077:ℚ)/8050157125000000000000000000000000000),((1201921832550781131974443:ℚ)/3696640000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((89977941:ℚ)/125000000),((919867851:ℚ)/1250000000),((-687867851:ℚ)/1323125000),((-189933823:ℚ)/445000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((3266074763:ℚ)/10000000000),((312152800176415642747810514097903491:ℚ)/1048047312500000000000000000000000000),((18623690064936502596883:ℚ)/57760000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/8),((-9:ℚ)/16),((7258238507:ℚ)/10000000000),((3709452979:ℚ)/5000000000),((-927150993:ℚ)/1780000000),((-46124146563:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((376288403:ℚ)/1250000000),((1538612386983246362963658585742141615377:ℚ)/5166477812500000000000000000000000000000),((327381275229929076554587:ℚ)/1024000000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((3659115241:ℚ)/5000000000),((7478858677:ℚ)/10000000000),((-5622858677:ℚ)/10775000000),((-23332037169:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2731531467:ℚ)/10000000000),((1895585292292116597398670042315977284981:ℚ)/6365702987500000000000000000000000000000),((29292813407038389342326683:ℚ)/92416000000000000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((7378211507:ℚ)/10000000000),((3799366959:ℚ)/5000000000),((-2871366959:ℚ)/5435000000),((-47203903563:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((242180717:ℚ)/1000000000),((4992286576447242381838092825180371975213:ℚ)/16620719150000000000000000000000000000000),((116151454787852712960351907:ℚ)/369664000000000000000000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((7498141859:ℚ)/10000000000),((195959269:ℚ)/250000000),((-149559269:ℚ)/276500000),((-48283276731:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((327810089:ℚ)/2000000000),((850149381546661627639823616142607531999:ℚ)/2783580800000000000000000000000000000000),((114092615323099564855262083:ℚ)/369664000000000000000000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((7737883279:ℚ)/10000000000),((4397825501:ℚ)/5000000000),((-3469825501:ℚ)/5720000000),((-16813649837:ℚ)/43200000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((24804628601995741779399147346772773769:ℚ)/74131200000000000000000000000000000000),((38893113:ℚ)/128000000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((4347759549:ℚ)/5000000000),((10706028327:ℚ)/10000000000),((-8850028327:ℚ)/12960000000),((-29529835941:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((237113536932919851717466513345329183221:ℚ)/648000000000000000000000000000000000000),((38893113:ℚ)/128000000)⟩
theorem valid12 : Valid source31 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((10606401557:ℚ)/10000000000),((1814771227:ℚ)/1250000000),((-1582771227:ℚ)/2000000000),((-25419204671:ℚ)/73600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1153201056650721875722974831:ℚ)/2708480000000000000000000000),((38893113:ℚ)/128000000)⟩
theorem valid13 : Valid source31 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source31 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source31 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source31 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC07
#check @N11Formalization.C450Source31GroupedC07.bound
#print axioms N11Formalization.C450Source31GroupedC07.valid0
#print axioms N11Formalization.C450Source31GroupedC07.valid1
#print axioms N11Formalization.C450Source31GroupedC07.valid2
#print axioms N11Formalization.C450Source31GroupedC07.valid3
#print axioms N11Formalization.C450Source31GroupedC07.valid4
#print axioms N11Formalization.C450Source31GroupedC07.valid5
#print axioms N11Formalization.C450Source31GroupedC07.valid6
#print axioms N11Formalization.C450Source31GroupedC07.valid7
#print axioms N11Formalization.C450Source31GroupedC07.valid8
#print axioms N11Formalization.C450Source31GroupedC07.valid9
#print axioms N11Formalization.C450Source31GroupedC07.valid10
#print axioms N11Formalization.C450Source31GroupedC07.valid11
#print axioms N11Formalization.C450Source31GroupedC07.valid12
#print axioms N11Formalization.C450Source31GroupedC07.valid13
#print axioms N11Formalization.C450Source31GroupedC07.bound
#print axioms N11Formalization.C450Source31GroupedC07.endpoint_checks
