import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((3034354639:ℚ)/5000000000),((659790897:ℚ)/1000000000),((8474354639:ℚ)/53400000000),((1235790897:ℚ)/4960000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3229865367:ℚ)/5000000000),((48758862342639192225014347391450350589:ℚ)/724913697792000000000000000000000000000),((-5521474263690798392547647:ℚ)/27724800000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((6546665199:ℚ)/10000000000),((6836603323:ℚ)/10000000000),((17426665199:ℚ)/110600000000),((12596603323:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5327702349:ℚ)/10000000000),((55608799736425061001449360989707106167634563423226857403191437:ℚ)/873122752930050000000000000000000000000000000000000000000000000),((-195952556796131452706135469:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((3392744763:ℚ)/5000000000),((278236801:ℚ)/400000000),((8832744763:ℚ)/56250000000),((508636801:ℚ)/2212000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2336058883:ℚ)/5000000000),((16246416707007183687951376696913809481701232180498137:ℚ)/260916238800000000000000000000000000000000000000000000),((-323033627500277067134261:ℚ)/1478656000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((6904867871:ℚ)/10000000000),((1768804443:ℚ)/2500000000),((17784867871:ℚ)/114400000000),((356533827:ℚ)/1562500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1077578857:ℚ)/2500000000),((7543363086247048747306164601696429208813050616359166061:ℚ)/121885538101196289062500000000000000000000000000000000000),((-38396263254577273407621767:ℚ)/173280000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((219507037:ℚ)/312500000),((3597248751:ℚ)/5000000000),((559507037:ℚ)/3634375000),((6477248751:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1958778267:ℚ)/5000000000),((3042900985725581646844925990879508422324227918593673970841747:ℚ)/49439896722287500000000000000000000000000000000000000000000000),((-155745531725253700331673983:ℚ)/693120000000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((3571781253:ℚ)/5000000000),((1828440023:ℚ)/2500000000),((9011781253:ℚ)/59100000000),((3268440023:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3483347083:ℚ)/10000000000),((34227940205146057856580497824871998599816903770663298453073:ℚ)/558911333526516723632812500000000000000000000000000000000000),((-13158622416285580169345669:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((726288081:ℚ)/1000000000),((7433006361:ℚ)/10000000000),((1814288081:ℚ)/12010000000),((4397668787:ℚ)/19700000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((597927481:ℚ)/2000000000),((12605820961235183247122752111725805164100872554650046837847997:ℚ)/206769256135743750000000000000000000000000000000000000000000000),((-640235534037706901199914543:ℚ)/2772480000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((7382181009:ℚ)/10000000000),((3776118539:ℚ)/5000000000),((18262181009:ℚ)/122000000000),((6656118539:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2399931361:ℚ)/10000000000),((38223552061143829650501550007157719305910451552884773734927:ℚ)/629489855402441406250000000000000000000000000000000000000000),((-2845820926214285591669599:ℚ)/12160000000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((3750731977:ℚ)/5000000000),((1605803643:ℚ)/2000000000),((9190731977:ℚ)/64800000000),((2757803643:ℚ)/12200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((806020561:ℚ)/5000000000),((383379779619070897950269024876916134485655802179604946997:ℚ)/6205093087500000000000000000000000000000000000000000000000),((-14425060868754931:ℚ)/60800000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((1994609627:ℚ)/2500000000),((1986888747:ℚ)/2000000000),((4714609627:ℚ)/40000000000),((1046296249:ℚ)/4320000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((6142181879942270580477514234645531253546392939049999:ℚ)/94478400000000000000000000000000000000000000000000000),((-15358891:ℚ)/64000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((9884452363:ℚ)/10000000000),((13740801721:ℚ)/10000000000),((6921484121:ℚ)/73600000000),((19500801721:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((5149028584202740643076950826334949309959:ℚ)/67712000000000000000000000000000000000000),((-15358891:ℚ)/64000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC18
#check @N11Formalization.C450Source19GroupedC18.bound
#print axioms N11Formalization.C450Source19GroupedC18.valid0
#print axioms N11Formalization.C450Source19GroupedC18.valid1
#print axioms N11Formalization.C450Source19GroupedC18.valid2
#print axioms N11Formalization.C450Source19GroupedC18.valid3
#print axioms N11Formalization.C450Source19GroupedC18.valid4
#print axioms N11Formalization.C450Source19GroupedC18.valid5
#print axioms N11Formalization.C450Source19GroupedC18.valid6
#print axioms N11Formalization.C450Source19GroupedC18.valid7
#print axioms N11Formalization.C450Source19GroupedC18.valid8
#print axioms N11Formalization.C450Source19GroupedC18.valid9
#print axioms N11Formalization.C450Source19GroupedC18.valid10
#print axioms N11Formalization.C450Source19GroupedC18.bound
#print axioms N11Formalization.C450Source19GroupedC18.endpoint_checks
