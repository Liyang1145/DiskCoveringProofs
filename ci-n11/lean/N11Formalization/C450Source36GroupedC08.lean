import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((3383550557:ℚ)/5000000000),((1399864807:ℚ)/2000000000),((-8246783263:ℚ)/19840000000),((-661183519:ℚ)/2106250000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((945110939:ℚ)/2000000000),((34214316292660096732521179815147162141:ℚ)/122023936000000000000000000000000000000),((270219006211291555242265181:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((6888011077:ℚ)/10000000000),((1764927829:ℚ)/2500000000),((-10444350461:ℚ)/25275000000),((-4088011077:ℚ)/12756250000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((2181549643:ℚ)/5000000000),((872567637428295960828556853011531637634438153702826421:ℚ)/3153577670288085937500000000000000000000000000000000000),((1056318984798132276739413101:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((6948435091:ℚ)/10000000000),((7120079453:ℚ)/10000000000),((-42320715077:ℚ)/102050000000),((-4148435091:ℚ)/12875000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((4170995789:ℚ)/10000000000),((8486923895072366450161893474848966881643619780905798947:ℚ)/30656808609375000000000000000000000000000000000000000000),((1043925593391753792141003389:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7008839247:ℚ)/10000000000),((1795107247:ℚ)/2500000000),((-10715965223:ℚ)/25750000000),((-4208839247:ℚ)/12993750000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((198512171:ℚ)/500000000),((57730552215227687601231025378949723751798735141785463:ℚ)/208421134948730468750000000000000000000000000000000000),((1031455568430521062373841621:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((706922411:ℚ)/1000000000),((7240760443:ℚ)/10000000000),((-43406843987:ℚ)/103950000000),((-426922411:ℚ)/1311250000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((150378013:ℚ)/400000000),((4211420881639505115084076151270619978036326173219104653:ℚ)/15195378515625000000000000000000000000000000000000000000),((10189088717264349869233549:ℚ)/36966400000000000000000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((3564795111:ℚ)/5000000000),((91263429:ℚ)/125000000),((-549370861:ℚ)/1311250000),((-2164795111:ℚ)/6615625000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1768407429:ℚ)/5000000000),((1953840800555842816612488029496959785750811407745469:ℚ)/7045414117431640625000000000000000000000000000000000),((251571366718285388890042149:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((7189938103:ℚ)/10000000000),((7361371103:ℚ)/10000000000),((-44492339927:ℚ)/105850000000),((-1463312701:ℚ)/4450000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((3299933847:ℚ)/10000000000),((771337029193689800892794510594651686024197939535753751749:ℚ)/2779610042871093750000000000000000000000000000000000000000),((993585319190675370277142021:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((7250268257:ℚ)/10000000000),((1870478809:ℚ)/2500000000),((-11394309281:ℚ)/26700000000),((-4450268257:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((304547741:ℚ)/1000000000),((50183997649479488203928856288153194676606690290136306403:ℚ)/178445278125000000000000000000000000000000000000000000000),((980808394599739662079603381:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source36 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((7370877299:ℚ)/10000000000),((760239637:ℚ)/1000000000),((-4666156733:ℚ)/10870000000),((-4570877299:ℚ)/13825000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3938759:ℚ)/16000000),((211868792333744876434595731964784283112072619678304279:ℚ)/752557911914062500000000000000000000000000000000000000),((955024086548602117969684669:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source36 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((7491421013:ℚ)/10000000000),((7843182553:ℚ)/10000000000),((-48828642977:ℚ)/110600000000),((-4691421013:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1692386327:ℚ)/10000000000),((174261292600243923479704710151544743784493140301891440271:ℚ)/603972775000000000000000000000000000000000000000000000000),((928932296632363328301483661:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid source36 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((1546465171:ℚ)/2000000000),((8804366987:ℚ)/10000000000),((-57479302883:ℚ)/114400000000),((-986465171:ℚ)/3240000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((31894415871969685161987558253959146489:ℚ)/98155200000000000000000000000000000000),((62683877:ℚ)/256000000)⟩
theorem valid10 : Valid source36 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((8693912899:ℚ)/10000000000),((10720281901:ℚ)/10000000000),((-74722537109:ℚ)/129600000000),((-5893912899:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((5085326070987601175898854317234407131:ℚ)/13996800000000000000000000000000000000),((62683877:ℚ)/256000000)⟩
theorem valid11 : Valid source36 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((5305198887:ℚ)/5000000000),((14538869253:ℚ)/10000000000),((-109089823277:ℚ)/160000000000),((-3905198887:ℚ)/13800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((14388217705226347015051306987477364683:ℚ)/32000000000000000000000000000000000000),((62683877:ℚ)/256000000)⟩
theorem valid12 : Valid source36 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source36 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source36 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source36 nn0 nn1 Qcell ((2117:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source36 nn0 nn1 Qcell ((2117:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC08
#check @N11Formalization.C450Source36GroupedC08.bound
#print axioms N11Formalization.C450Source36GroupedC08.valid0
#print axioms N11Formalization.C450Source36GroupedC08.valid1
#print axioms N11Formalization.C450Source36GroupedC08.valid2
#print axioms N11Formalization.C450Source36GroupedC08.valid3
#print axioms N11Formalization.C450Source36GroupedC08.valid4
#print axioms N11Formalization.C450Source36GroupedC08.valid5
#print axioms N11Formalization.C450Source36GroupedC08.valid6
#print axioms N11Formalization.C450Source36GroupedC08.valid7
#print axioms N11Formalization.C450Source36GroupedC08.valid8
#print axioms N11Formalization.C450Source36GroupedC08.valid9
#print axioms N11Formalization.C450Source36GroupedC08.valid10
#print axioms N11Formalization.C450Source36GroupedC08.valid11
#print axioms N11Formalization.C450Source36GroupedC08.valid12
#print axioms N11Formalization.C450Source36GroupedC08.bound
#print axioms N11Formalization.C450Source36GroupedC08.endpoint_checks
