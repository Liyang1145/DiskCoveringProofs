import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((2003:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((712291429:ℚ)/1000000000),((364861471:ℚ)/500000000),((-921784413:ℚ)/992000000),((-4090040003:ℚ)/5007500000),((398569427:ℚ)/400000000),(1:ℚ),((845998389:ℚ)/10000000000),((445261259:ℚ)/1250000000),((119459591476243120582123260563916365941:ℚ)/311397093546250000000000000000000000000),((7297936893667702060291219:ℚ)/7393280000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((2003:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((2003:ℚ)/3200),((1011:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((897812441:ℚ)/1250000000),((3678359383:ℚ)/5000000000),((-9307078149:ℚ)/10015000000),((-5164687087:ℚ)/6318750000),((9929701407:ℚ)/10000000000),((62276473:ℚ)/62500000),((18538009:ℚ)/156250000),((83250177:ℚ)/250000000),((47309013029765773949251896189433337075382485920025771:ℚ)/123371407687246799468994140625000000000000000000000000),((732112810754863508096674051:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((2003:ℚ)/3200) ((1011:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((3621040397:ℚ)/5000000000),((7416205977:ℚ)/10000000000),((-6264205977:ℚ)/6740000000),((-20867282779:ℚ)/25512500000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((616240193:ℚ)/2000000000),((5337126018502990496589929784042518038371017822780968651:ℚ)/13923529404449462890625000000000000000000000000000000000),((2937753162718336718621224611:ℚ)/2957312000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((7301658201:ℚ)/10000000000),((7475691113:ℚ)/10000000000),((-18971073339:ℚ)/20410000000),((-42151607407:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((175701841:ℚ)/625000000),((80115837686896765320255126842128514467136269182784578462169:ℚ)/209086481906250000000000000000000000000000000000000000000000),((8163657959031908819916811:ℚ)/8192000000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((1472246371:ℚ)/2000000000),((949331923:ℚ)/1250000000),((-2415995769:ℚ)/2575000000),((-8513724597:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2513275023:ℚ)/10000000000),((1129749398533350577120530746086160544051111706831406999:ℚ)/2902710616381835937500000000000000000000000000000000000),((46340806111812834014115211:ℚ)/46208000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((1870092079:ℚ)/2500000000),((7713612011:ℚ)/10000000000),((-19684836033:ℚ)/20980000000),((-10850644553:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((88832657:ℚ)/500000000),((2021672457518318174301158972628599635759185571945593000751:ℚ)/5199697132031250000000000000000000000000000000000000000000),((1027235293:ℚ)/1024000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((3799745481:ℚ)/5000000000),((8189369723:ℚ)/10000000000),((-7037369723:ℚ)/7120000000),((-22118218367:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),((57870301:ℚ)/5000000000),((16484928483307611952899332101756043289989139825041631442009:ℚ)/39038163450000000000000000000000000000000000000000000000000),((1027235293:ℚ)/1024000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((8075857239:ℚ)/10000000000),((4570309013:ℚ)/5000000000),(-1:ℚ),((-47571000673:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((557617089927670306905878977410864023944460402710214415439:ℚ)/1275458400000000000000000000000000000000000000000000000000),((1027235293:ℚ)/1024000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((9028107383:ℚ)/10000000000),((2760600529:ℚ)/2500000000),(-1:ℚ),((-54236751681:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((89790196274304415883077918817049123399449355815914502141:ℚ)/200000000000000000000000000000000000000000000000000000000),((1027235293:ℚ)/1024000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((10931321893:ℚ)/10000000000),((14844495281:ℚ)/10000000000),(-1:ℚ),((-2937358837:ℚ)/4800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((12912324282149379144345590275816499:ℚ)/27648000000000000000000000000000000),((1027235293:ℚ)/1024000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
private theorem node0_2 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source29 nn0 nn1 Qcell ((2041:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source29 nn0 nn1 Qcell ((1011:ℚ)/1600) ((1049:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_10
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_10
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9]
theorem packet_count : packets.length = 10 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC02
#check @N11Formalization.C450Source29GroupedC02.bound
#print axioms N11Formalization.C450Source29GroupedC02.valid0
#print axioms N11Formalization.C450Source29GroupedC02.valid1
#print axioms N11Formalization.C450Source29GroupedC02.valid2
#print axioms N11Formalization.C450Source29GroupedC02.valid3
#print axioms N11Formalization.C450Source29GroupedC02.valid4
#print axioms N11Formalization.C450Source29GroupedC02.valid5
#print axioms N11Formalization.C450Source29GroupedC02.valid6
#print axioms N11Formalization.C450Source29GroupedC02.valid7
#print axioms N11Formalization.C450Source29GroupedC02.valid8
#print axioms N11Formalization.C450Source29GroupedC02.valid9
#print axioms N11Formalization.C450Source29GroupedC02.bound
#print axioms N11Formalization.C450Source29GroupedC02.endpoint_checks
