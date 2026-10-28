import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((3484354639:ℚ)/5000000000),((3597463269:ℚ)/5000000000),((-38127022497:ℚ)/49600000000),((-8213063917:ℚ)/12637500000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2052324237:ℚ)/5000000000),((5644711371464644082238945304320268049:ℚ)/15641745244628906250000000000000000000),((2494574461821546377126056261:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((7088240321:ℚ)/10000000000),((7254618077:ℚ)/10000000000),((-77030035001:ℚ)/101100000000),((-16784720963:ℚ)/25512500000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((3690701239:ℚ)/10000000000),((14860231843458679198510863505180002936242385601459456969:ℚ)/41770588213348388671875000000000000000000000000000000000),((9972764057510208197151319781:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((7147994831:ℚ)/10000000000),((7314303731:ℚ)/10000000000),((-77805948503:ℚ)/102050000000),((-16963984493:ℚ)/25750000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((866555179:ℚ)/2500000000),((9292501881749106716126107921715317552117303397791953369731:ℚ)/26135810238281250000000000000000000000000000000000000000000),((9976350468607662541592748101:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((288309691:ℚ)/400000000),((7373983663:ℚ)/10000000000),((-78581787619:ℚ)/103000000000),((-685729073:ℚ)/1039500000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((1613428861:ℚ)/5000000000),((1003692575074419724689139588662526847454527314095971:ℚ)/2824559695486450195312500000000000000000000000000000),((15967773180602232516713821:ℚ)/23658496000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((227108839:ℚ)/312500000),((743365803:ℚ)/1000000000),((-2645251813:ℚ)/3465000000),((-541326517:ℚ)/819531250),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((18556307:ℚ)/62500000),((423344717983109704593560632998735968732105287800024103:ℚ)/1192009761567413806915283203125000000000000000000000000),((9749304097697294286827861:ℚ)/14440000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((366360837:ℚ)/500000000),((936665873:ℚ)/1250000000),((-10016656349:ℚ)/13112500000),((-30175259:ℚ)/45625000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((2687352813:ℚ)/10000000000),((221031176354582616281600117500220429576430698894031:ℚ)/622678883361816406250000000000000000000000000000000),((74899784793929465803457687:ℚ)/110899200000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((7386944131:ℚ)/10000000000),((7552990669:ℚ)/10000000000),((-80908878697:ℚ)/105850000000),((-17680832393:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((2373420999:ℚ)/10000000000),((67014789084533326313939419052909001301055200393091429584723:ℚ)/188884326895312500000000000000000000000000000000000000000000),((9989909995630148200121698701:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((7446665199:ℚ)/10000000000),((311663819:ℚ)/400000000),((-3360429647:ℚ)/4272000000),((-17859995597:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((402431031:ℚ)/2000000000),((12962863936949983098968957395265102895159476304349608980339:ℚ)/35275784889843750000000000000000000000000000000000000000000),((29971083276339647430422974223:ℚ)/44359680000000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((3842744763:ℚ)/5000000000),((4015063203:ℚ)/5000000000),((-43555821639:ℚ)/55300000000),((-9288234289:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((3703502949682001622122992259247705384664216708785844020757:ℚ)/10106790443750000000000000000000000000000000000000000000000),((690096431:ℚ)/1024000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((247632037:ℚ)/312500000),((8983642303:ℚ)/10000000000),((-99507349939:ℚ)/114400000000),((-602896111:ℚ)/1012500000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((285782775116535477929498628713296101944781443269781711:ℚ)/695764736938476562500000000000000000000000000000000000),((690096431:ℚ)/1024000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((2219609627:ℚ)/2500000000),((10888662237:ℚ)/10000000000),((-41424203027:ℚ)/43200000000),((-5538828881:ℚ)/10000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((4777988974345363158798054130154507293142715516298363007:ℚ)/10546875000000000000000000000000000000000000000000000000),((690096431:ℚ)/1024000000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((10784452363:ℚ)/10000000000),((14694545697:ℚ)/10000000000),(-1:ℚ),((-27873357089:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((20333619281042803823993400933350848927:ℚ)/42049152000000000000000000000000000000),((690096431:ℚ)/1024000000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source29 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source29 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source29 nn0 nn1 Qcell ((2117:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source29 nn0 nn1 Qcell ((2117:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC04
#check @N11Formalization.C450Source29GroupedC04.bound
#print axioms N11Formalization.C450Source29GroupedC04.valid0
#print axioms N11Formalization.C450Source29GroupedC04.valid1
#print axioms N11Formalization.C450Source29GroupedC04.valid2
#print axioms N11Formalization.C450Source29GroupedC04.valid3
#print axioms N11Formalization.C450Source29GroupedC04.valid4
#print axioms N11Formalization.C450Source29GroupedC04.valid5
#print axioms N11Formalization.C450Source29GroupedC04.valid6
#print axioms N11Formalization.C450Source29GroupedC04.valid7
#print axioms N11Formalization.C450Source29GroupedC04.valid8
#print axioms N11Formalization.C450Source29GroupedC04.valid9
#print axioms N11Formalization.C450Source29GroupedC04.valid10
#print axioms N11Formalization.C450Source29GroupedC04.valid11
#print axioms N11Formalization.C450Source29GroupedC04.bound
#print axioms N11Formalization.C450Source29GroupedC04.endpoint_checks
