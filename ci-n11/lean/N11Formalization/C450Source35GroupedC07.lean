import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((6845688201:ℚ)/10000000000),((3539462297:ℚ)/5000000000),((-80111687:ℚ)/160000000),((-39851193809:ℚ)/101100000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4493067003:ℚ)/10000000000),((2152594437494205966232017001139:ℚ)/6400000000000000000000000000000),((23870948536237213439577:ℚ)/64000000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((6966285647:ℚ)/10000000000),((44619673:ℚ)/62500000),((-31419673:ℚ)/63187500),((-40936570823:ℚ)/102050000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((4112632889:ℚ)/10000000000),((3641599424820855996280948413526348917272797453:ℚ)/10949922466278076171875000000000000000000000000),((23508744412989794553193:ℚ)/64000000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((7026557983:ℚ)/10000000000),((7199354793:ℚ)/10000000000),((-5087354793:ℚ)/10205000000),((-41479021847:ℚ)/103000000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((3909509463:ℚ)/10000000000),((6794498074592492916012304890739422149755460151913461:ℚ)/20437872406250000000000000000000000000000000000000000),((8420615224074434195563633:ℚ)/23104000000000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((1771703349:ℚ)/2500000000),((362977319:ℚ)/500000000),((-257377319:ℚ)/515000000),((-10505330141:ℚ)/25987500000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((3695902293:ℚ)/10000000000),((1108267571773244545797296739306681802044162514991:ℚ)/3334738159179687500000000000000000000000000000000),((522133191911558029439097:ℚ)/1444000000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((1786763091:ℚ)/2500000000),((1829930719:ℚ)/2500000000),((-1301930719:ℚ)/2598750000),((-10640867819:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3469869169:ℚ)/10000000000),((213699983830373184226216327782031:ℚ)/643190625000000000000000000000000),((517950258015484247283657:ℚ)/1444000000000000000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((3603637673:ℚ)/5000000000),((3689942349:ℚ)/5000000000),((-2633942349:ℚ)/5245000000),((-21552739057:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((403599321:ℚ)/1250000000),((2284541945115334503793442922734247:ℚ)/6877506250000000000000000000000000),((2054958564821019979943713:ℚ)/5776000000000000000000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((3633741393:ℚ)/5000000000),((930004031:ℚ)/1250000000),((-666004031:ℚ)/1323125000),((-21823672537:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((2969009399:ℚ)/10000000000),((15929462565365359077557754126251:ℚ)/47963281250000000000000000000000),((5645444133466098612873:ℚ)/16000000000000000000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((7327675109:ℚ)/10000000000),((7560286067:ℚ)/10000000000),((-5448286067:ℚ)/10680000000),((-44189075981:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1342540177:ℚ)/5000000000),((3186833430017839386096977358760601:ℚ)/9505200000000000000000000000000000),((22392701411483122357537:ℚ)/64000000000000000000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((3724008017:ℚ)/5000000000),((1536097453:ℚ)/2000000000),((-1113697453:ℚ)/2174000000),((-22636072153:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((400648481:ℚ)/2000000000),((49503445235574548672636864114311:ℚ)/147696125000000000000000000000000),((1986480728130558231331633:ℚ)/5776000000000000000000000)⟩
theorem valid8 : Valid source35 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((7568301233:ℚ)/10000000000),((3960371269:ℚ)/5000000000),((-2904371269:ℚ)/5530000000),((-46354711097:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((730921:ℚ)/8000000),((372744766458918083037633311316079:ℚ)/1092175000000000000000000000000000),((7806306430151708998687633:ℚ)/23104000000000000000000000)⟩
theorem valid9 : Valid source35 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((3904357917:ℚ)/5000000000),((1776024907:ℚ)/2000000000),((-1353624907:ℚ)/2288000000),((-24259221253:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((493215342613891610113509476184083:ℚ)/1308736000000000000000000000000000),((430427:ℚ)/1280000)⟩
theorem valid10 : Valid source35 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((1753727787:ℚ)/2000000000),((10793485307:ℚ)/10000000000),((-8681485307:ℚ)/12960000000),((-11431550083:ℚ)/32000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1940748775111549231830705811841593:ℚ)/4665600000000000000000000000000000),((430427:ℚ)/1280000)⟩
theorem valid11 : Valid source35 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((2670691727:ℚ)/2500000000),((3652275611:ℚ)/2500000000),((-3124275611:ℚ)/4000000000),((-18596225543:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((199472685976199285951093:ℚ)/400000000000000000000000),((430427:ℚ)/1280000)⟩
theorem valid12 : Valid source35 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source35 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source35 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source35 nn0 nn1 Qcell ((2117:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source35 nn0 nn1 Qcell ((2117:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC07
#check @N11Formalization.C450Source35GroupedC07.bound
#print axioms N11Formalization.C450Source35GroupedC07.valid0
#print axioms N11Formalization.C450Source35GroupedC07.valid1
#print axioms N11Formalization.C450Source35GroupedC07.valid2
#print axioms N11Formalization.C450Source35GroupedC07.valid3
#print axioms N11Formalization.C450Source35GroupedC07.valid4
#print axioms N11Formalization.C450Source35GroupedC07.valid5
#print axioms N11Formalization.C450Source35GroupedC07.valid6
#print axioms N11Formalization.C450Source35GroupedC07.valid7
#print axioms N11Formalization.C450Source35GroupedC07.valid8
#print axioms N11Formalization.C450Source35GroupedC07.valid9
#print axioms N11Formalization.C450Source35GroupedC07.valid10
#print axioms N11Formalization.C450Source35GroupedC07.valid11
#print axioms N11Formalization.C450Source35GroupedC07.valid12
#print axioms N11Formalization.C450Source35GroupedC07.bound
#print axioms N11Formalization.C450Source35GroupedC07.endpoint_checks
