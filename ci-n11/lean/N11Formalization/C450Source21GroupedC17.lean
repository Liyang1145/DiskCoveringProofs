import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((3049186883:ℚ)/5000000000),((1657898237:ℚ)/2500000000),((152:ℚ)/1335),((4857898237:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6394608811:ℚ)/10000000000),((27093213541867651990658586643270316200201:ℚ)/271842636672000000000000000000000000000000),((-205085100399644499942402973:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((822134393:ℚ)/1250000000),((687059359:ℚ)/1000000000),((304:ℚ)/2765),((655686453:ℚ)/3560000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((328024377:ℚ)/625000000),((1175632213044569865162133603562904435225934091904816449861:ℚ)/12319192281200000000000000000000000000000000000000000000000),((-35375584926107334622525877:ℚ)/147865600000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((1704058261:ℚ)/2500000000),((139801111:ℚ)/200000000),((608:ℚ)/5625),((395801111:ℚ)/2212000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4581488669:ℚ)/10000000000),((73409398670337636966172766324890522286482016263477543:ℚ)/782748716400000000000000000000000000000000000000000000),((-1466195030500262943340357:ℚ)/5914624000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((6935769573:ℚ)/10000000000),((1421898731:ℚ)/2000000000),((76:ℚ)/715),((1327299577:ℚ)/7500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4211944013:ℚ)/10000000000),((1676543201836298014556524480048486405070343389093674683029:ℚ)/17972753906250000000000000000000000000000000000000000000000),((-149125184601442212789729037:ℚ)/591462400000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((282211189:ℚ)/400000000),((225903409:ℚ)/312500000),((608:ℚ)/5815),((625903409:ℚ)/3575000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3809111673:ℚ)/10000000000),((8963855501901297117584842944899482002228839588978972402599:ℚ)/96562298285717773437500000000000000000000000000000000000000),((-3701869591703007754202677:ℚ)/14440000000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((896845601:ℚ)/1250000000),((7348302953:ℚ)/10000000000),((304:ℚ)/2955),((20148302953:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((210062673:ℚ)/625000000),((26448015151564986795632228231436867980729213128523077681760749:ℚ)/286162602765576562500000000000000000000000000000000000000000000),((-202802254226135701610998087:ℚ)/778240000000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((3647113023:ℚ)/5000000000),((3793515027:ℚ)/5000000000),((152:ℚ)/1525),((10193515027:ℚ)/59100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1423132733:ℚ)/5000000000),((443833310977556219225827209899467042094040609497494404417637:ℚ)/4800673057443750000000000000000000000000000000000000000000000),((-2934741180485385175322991479:ℚ)/11089920000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((1506616299:ℚ)/2000000000),((8064266863:ℚ)/10000000000),((38:ℚ)/405),((20864266863:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1328007413:ℚ)/10000000000),((1722497289378659975894233250023826985412038544546754056124753:ℚ)/18615279262500000000000000000000000000000000000000000000000000),((-3324807995578207:ℚ)/12160000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((1001319011:ℚ)/1250000000),((9971078179:ℚ)/10000000000),((19:ℚ)/250),((7590359393:ℚ)/43200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2988724043772623918530559253788578678375700336187977687:ℚ)/31492800000000000000000000000000000000000000000000000000),((-56502291:ℚ)/204800000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((4959037017:ℚ)/5000000000),((6889528287:ℚ)/5000000000),((19:ℚ)/345),((13289528287:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((65539993686498613834488120008322451328299:ℚ)/609408000000000000000000000000000000000000),((-56502291:ℚ)/204800000)⟩
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
end N11Formalization.C450Source21GroupedC17
#check @N11Formalization.C450Source21GroupedC17.bound
#print axioms N11Formalization.C450Source21GroupedC17.valid0
#print axioms N11Formalization.C450Source21GroupedC17.valid1
#print axioms N11Formalization.C450Source21GroupedC17.valid2
#print axioms N11Formalization.C450Source21GroupedC17.valid3
#print axioms N11Formalization.C450Source21GroupedC17.valid4
#print axioms N11Formalization.C450Source21GroupedC17.valid5
#print axioms N11Formalization.C450Source21GroupedC17.valid6
#print axioms N11Formalization.C450Source21GroupedC17.valid7
#print axioms N11Formalization.C450Source21GroupedC17.valid8
#print axioms N11Formalization.C450Source21GroupedC17.valid9
#print axioms N11Formalization.C450Source21GroupedC17.bound
#print axioms N11Formalization.C450Source21GroupedC17.endpoint_checks
