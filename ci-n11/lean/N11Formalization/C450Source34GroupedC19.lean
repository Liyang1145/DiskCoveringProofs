import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/8),((3:ℚ)/16),((5815408231:ℚ)/10000000000),((6150990911:ℚ)/10000000000),((16055408231:ℚ)/51500000000),((39572972733:ℚ)/99200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6994672381:ℚ)/10000000000),((-582496148247065323926833835662574309642764843111475919382701:ℚ)/2461196828906250000000000000000000000000000000000000000000000),((-4278225272142909891558764099:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((6058073921:ℚ)/10000000000),((3136038483:ℚ)/5000000000),((16298073921:ℚ)/52450000000),((19968115449:ℚ)/51500000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((51863533:ℚ)/80000000),((-562387040191683463781606250838664927399996006289781418408337:ℚ)/2391833547898632812500000000000000000000000000000000000000000),((-57639678696367351814192889:ℚ)/194560000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((6179262037:ℚ)/10000000000),((1598269381:ℚ)/2500000000),((16419262037:ℚ)/53400000000),((10074808143:ℚ)/26225000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((248562347:ℚ)/400000000),((-60737671409032851483828013534340568043315520560405907560113781:ℚ)/261815149992037500000000000000000000000000000000000000000000000),((-275825339752808956851579659:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((1575090203:ℚ)/2500000000),((1302799447:ℚ)/2000000000),((4135090203:ℚ)/13587500000),((2710799447:ℚ)/7120000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5934883533:ℚ)/10000000000),((-28440103466557846391153785344004815140401497474481248177459:ℚ)/124187733755651855468750000000000000000000000000000000000000),((-177802975800560745089862771:ℚ)/591462400000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((6421375113:ℚ)/10000000000),((207338763:ℚ)/312500000),((16661375113:ℚ)/55300000000),((1282016289:ℚ)/3396875000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((352740559:ℚ)/625000000),((-13240916578949650476332663697441003098833466178790017399813827:ℚ)/58540412747904199218750000000000000000000000000000000000000000),((-4371313730544094441987861:ℚ)/14440000000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((6542309457:ℚ)/10000000000),((6755611079:ℚ)/10000000000),((16782309457:ℚ)/56250000000),((41386833237:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1067795057:ℚ)/2000000000),((-11278099119052330244148916364894660470997497810448959998533:ℚ)/50460559129714965820312500000000000000000000000000000000000),((-4506660632189679737521268179:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((6663168041:ℚ)/10000000000),((6876312957:ℚ)/10000000000),((16903168041:ℚ)/57200000000),((13916312957:ℚ)/37500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2508849663:ℚ)/5000000000),((-775350574539399348854437509414478514384440175363272585651:ℚ)/3509048400000000000000000000000000000000000000000000000000),((-4536382928492047934442189531:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((1695988693:ℚ)/2500000000),((1749237383:ℚ)/2500000000),((4255988693:ℚ)/14537500000),((10527712149:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1169149847:ℚ)/2500000000),((-85812438046262269256867449181760800950716227051308928077669:ℚ)/392664171001013183593750000000000000000000000000000000000000),((-285337149887813743211505491:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((690467329:ℚ)/1000000000),((7117524049:ℚ)/10000000000),((1714467329:ℚ)/5910000000),((42472572147:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2155464087:ℚ)/5000000000),((-53207154099630499040689300049261769757058091739074412829:ℚ)/246055548379687500000000000000000000000000000000000000000),((-4593697138290301460369837219:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((7025326993:ℚ)/10000000000),((1471699771:ℚ)/2000000000),((17265326993:ℚ)/61000000000),((2879699771:ℚ)/7880000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3913757761:ℚ)/10000000000),((-34773779099143131841269596898259259152977311358676779339956923:ℚ)/165166980543750000000000000000000000000000000000000000000000000),((-183182307532537667259043979:ℚ)/591462400000000000000000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((1816613109:ℚ)/2500000000),((7839825001:ℚ)/10000000000),((4376613109:ℚ)/16200000000),((44639475003:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((2973639927:ℚ)/10000000000),((-6610190227636421578135194902369329606713117471732107274311:ℚ)/32958199350000000000000000000000000000000000000000000000000),((-76168250352696107:ℚ)/243200000000000000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((7748052277:ℚ)/10000000000),((9759032213:ℚ)/10000000000),((17988052277:ℚ)/80000000000),((16799032213:ℚ)/43200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-43789542696456405794845952970192159233532717794741862484981:ℚ)/259200000000000000000000000000000000000000000000000000000000),((-66770701:ℚ)/204800000)⟩
theorem valid11 : Valid source34 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((37765963:ℚ)/39062500),((543257639:ℚ)/400000000),((77765963:ℚ)/431250000),((2474572917:ℚ)/6400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-13439067602976398831248012215799556175996403632920497:ℚ)/96242871093750000000000000000000000000000000000000000),((-66770701:ℚ)/204800000)⟩
theorem valid12 : Valid source34 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC19
#check @N11Formalization.C450Source34GroupedC19.bound
#print axioms N11Formalization.C450Source34GroupedC19.valid0
#print axioms N11Formalization.C450Source34GroupedC19.valid1
#print axioms N11Formalization.C450Source34GroupedC19.valid2
#print axioms N11Formalization.C450Source34GroupedC19.valid3
#print axioms N11Formalization.C450Source34GroupedC19.valid4
#print axioms N11Formalization.C450Source34GroupedC19.valid5
#print axioms N11Formalization.C450Source34GroupedC19.valid6
#print axioms N11Formalization.C450Source34GroupedC19.valid7
#print axioms N11Formalization.C450Source34GroupedC19.valid8
#print axioms N11Formalization.C450Source34GroupedC19.valid9
#print axioms N11Formalization.C450Source34GroupedC19.valid10
#print axioms N11Formalization.C450Source34GroupedC19.valid11
#print axioms N11Formalization.C450Source34GroupedC19.valid12
#print axioms N11Formalization.C450Source34GroupedC19.bound
#print axioms N11Formalization.C450Source34GroupedC19.endpoint_checks
