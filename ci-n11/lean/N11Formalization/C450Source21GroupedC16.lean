import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC16
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((-1:ℚ)/16),(0:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/16),(0:ℚ),((6148170457:ℚ)/10000000000),((333963153:ℚ)/500000000),((274036847:ℚ)/5340000000),((4:ℚ)/31),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1256797647:ℚ)/2000000000),((44245162426965305249169413677:ℚ)/424754119800000000000000000000),((-11515606646720701:ℚ)/60800000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((6626886521:ℚ)/10000000000),((1383651557:ℚ)/2000000000),((1048348443:ℚ)/22120000000),((32:ℚ)/267),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2558036303:ℚ)/5000000000),((668037231769466379261660945811833875917801:ℚ)/6652363831848000000000000000000000000000000),((-12589219812441053:ℚ)/60800000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/16),(0:ℚ),((6866050991:ℚ)/10000000000),((7037716939:ℚ)/10000000000),((1707427687:ℚ)/37500000000),((64:ℚ)/553),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((443098003:ℚ)/1000000000),((16811159136302395577302908982758312912279113:ℚ)/169867342968750000000000000000000000000000000),((-13125592295158763:ℚ)/60800000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/16),(0:ℚ),((1746397659:ℚ)/2500000000),((1789288083:ℚ)/2500000000),((96208609:ℚ)/2200000000),((128:ℚ)/1125),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4048622551:ℚ)/10000000000),((72390044460233769957526288177008790217:ℚ)/735075000000000000000000000000000000000),((-3348420755055687:ℚ)/15200000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((7105103797:ℚ)/10000000000),((7276565143:ℚ)/10000000000),((4883434857:ℚ)/116300000000),((16:ℚ)/143),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((18143481:ℚ)/50000000),((9694080646421542782267473688880151581871317:ℚ)/98879793444575000000000000000000000000000000),((-13661714349805321:ℚ)/60800000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((722459179:ℚ)/1000000000),((7395956473:ℚ)/10000000000),((1588014509:ℚ)/39400000000),((128:ℚ)/1163),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3156197653:ℚ)/10000000000),((596080870200291985696807870645889411264713729:ℚ)/6104802192332300000000000000000000000000000000),((-1392968923529047:ℚ)/6080000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/16),(0:ℚ),((3672027921:ℚ)/5000000000),((954334843:ℚ)/1250000000),((565665157:ℚ)/15250000000),((64:ℚ)/591),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2602598737:ℚ)/10000000000),((23415018900536551892253151756241509301629679:ℚ)/240033652872187500000000000000000000000000000),((-7098805214231253:ℚ)/30400000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/16),(0:ℚ),((7582916653:ℚ)/10000000000),((4055953377:ℚ)/5000000000),((2024046623:ℚ)/64800000000),((32:ℚ)/305),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((167654833:ℚ)/2500000000),((232077479121405897552506320615392582544801:ℚ)/2382755745600000000000000000000000000000000),((-14733301897266529:ℚ)/60800000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/16),(0:ℚ),((806039701:ℚ)/1000000000),((5009345659:ℚ)/5000000000),((1070654341:ℚ)/80000000000),((8:ℚ)/81),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((418905881466630927146991491636548642462753:ℚ)/4251528000000000000000000000000000000000000),((-3887267:ℚ)/16000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/16),(0:ℚ),((9967948633:ℚ)/10000000000),((6913441407:ℚ)/5000000000),((-833441407:ℚ)/80000000000),((2:ℚ)/25),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((8685987682482839:ℚ)/80000000000000000),((-3887267:ℚ)/16000000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
private theorem node0_2 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source21 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_10
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_10
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9]
theorem packet_count : packets.length = 10 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC16
#check @N11Formalization.C450Source21GroupedC16.bound
#print axioms N11Formalization.C450Source21GroupedC16.valid0
#print axioms N11Formalization.C450Source21GroupedC16.valid1
#print axioms N11Formalization.C450Source21GroupedC16.valid2
#print axioms N11Formalization.C450Source21GroupedC16.valid3
#print axioms N11Formalization.C450Source21GroupedC16.valid4
#print axioms N11Formalization.C450Source21GroupedC16.valid5
#print axioms N11Formalization.C450Source21GroupedC16.valid6
#print axioms N11Formalization.C450Source21GroupedC16.valid7
#print axioms N11Formalization.C450Source21GroupedC16.valid8
#print axioms N11Formalization.C450Source21GroupedC16.valid9
#print axioms N11Formalization.C450Source21GroupedC16.bound
#print axioms N11Formalization.C450Source21GroupedC16.endpoint_checks
