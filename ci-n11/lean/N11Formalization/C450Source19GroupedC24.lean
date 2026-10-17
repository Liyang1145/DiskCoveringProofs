import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((5808565471:ℚ)/10000000000),((793679247:ℚ)/1250000000),((17179986099:ℚ)/35600000000),((973679247:ℚ)/1550000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((70086457:ℚ)/100000000),((1679948068106350643729753:ℚ)/126736000000000000000000000),((-106783345016385133428151:ℚ)/338437500000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((6285812589:ℚ)/10000000000),((6587902133:ℚ)/10000000000),((54880688123:ℚ)/110600000000),((8027902133:ℚ)/13350000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5969025519:ℚ)/10000000000),((264796968886447786465887753685281637:ℚ)/36697080000000000000000000000000000000),((-2320592384812416643858307:ℚ)/7220000000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((652431959:ℚ)/1000000000),((1706576401:ℚ)/2500000000),((5655023713:ℚ)/11440000000),((2066576401:ℚ)/3456250000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5385308393:ℚ)/10000000000),((66142213780498751397894538100481:ℚ)/10067200000000000000000000000000000),((-146141336585764719767563:ℚ)/451250000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((3381379647:ℚ)/5000000000),((6945485079:ℚ)/10000000000),((29109657529:ℚ)/58150000000),((8385485079:ℚ)/14300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((592261337:ℚ)/1250000000),((3828968747776278017409099146553872660813987687840846471:ℚ)/921701804882812500000000000000000000000000000000000000000),((-7077905862537998336434849:ℚ)/21660000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((1720488997:ℚ)/2500000000),((7064650673:ℚ)/10000000000),((4921140993:ℚ)/9850000000),((8504650673:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((547739287:ℚ)/1250000000),((579412391810353885364415571874819:ℚ)/145533750000000000000000000000000000),((-2367977520926637631026427:ℚ)/7220000000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((3500569121:ℚ)/5000000000),((1795950763:ℚ)/2500000000),((29943983847:ℚ)/60050000000),((2155950763:ℚ)/3693750000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((499545903:ℚ)/1250000000),((41478484743451588844718644401168057:ℚ)/10818007500000000000000000000000000000),((-148536898151658074682547:ℚ)/451250000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((7120306747:ℚ)/10000000000),((1460588567:ℚ)/2000000000),((60722147229:ℚ)/122000000000),((1748588567:ℚ)/3002500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((357191577:ℚ)/1000000000),((55245333184023841807208355111001971:ℚ)/14884000000000000000000000000000000000),((-95405622994414351357707:ℚ)/288800000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((144789243:ℚ)/200000000),((7422070607:ℚ)/10000000000),((1231124701:ℚ)/2478000000),((8862070607:ℚ)/15250000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((3092542283:ℚ)/10000000000),((3697218394144316193527040603533:ℚ)/1023414000000000000000000000000000),((-2393628201682234169416187:ℚ)/7220000000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((7358605057:ℚ)/10000000000),((3770593457:ℚ)/5000000000),((3670013847:ℚ)/7400000000),((641513351:ℚ)/1106250000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((505427139:ℚ)/2000000000),((6050629339317838624612204830263:ℚ)/1711250000000000000000000000000000),((-600513328545115802887387:ℚ)/1805000000000000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((7477736039:ℚ)/10000000000),((3889693583:ℚ)/5000000000),((63224152273:ℚ)/129600000000),((4609693583:ℚ)/7862500000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1796144939:ℚ)/10000000000),((28929086022496913097484118616546289:ℚ)/5598720000000000000000000000000000000),((-2539381944403907:ℚ)/7600000000000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((482247771:ℚ)/625000000),((302618369:ℚ)/312500000),((4055734397:ℚ)/10000000000),((347618369:ℚ)/506250000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1715275891744936393386400451018401:ℚ)/75000000000000000000000000000000000),((-671753:ℚ)/2000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((1924108213:ℚ)/2000000000),((1686118309:ℚ)/1250000000),((15644757491:ℚ)/44160000000),((1866118309:ℚ)/2500000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2704043795743295273996531:ℚ)/65003520000000000000000000),((-671753:ℚ)/2000000)⟩
theorem valid11 : Valid source19 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC24
#check @N11Formalization.C450Source19GroupedC24.bound
#print axioms N11Formalization.C450Source19GroupedC24.valid0
#print axioms N11Formalization.C450Source19GroupedC24.valid1
#print axioms N11Formalization.C450Source19GroupedC24.valid2
#print axioms N11Formalization.C450Source19GroupedC24.valid3
#print axioms N11Formalization.C450Source19GroupedC24.valid4
#print axioms N11Formalization.C450Source19GroupedC24.valid5
#print axioms N11Formalization.C450Source19GroupedC24.valid6
#print axioms N11Formalization.C450Source19GroupedC24.valid7
#print axioms N11Formalization.C450Source19GroupedC24.valid8
#print axioms N11Formalization.C450Source19GroupedC24.valid9
#print axioms N11Formalization.C450Source19GroupedC24.valid10
#print axioms N11Formalization.C450Source19GroupedC24.valid11
#print axioms N11Formalization.C450Source19GroupedC24.bound
#print axioms N11Formalization.C450Source19GroupedC24.endpoint_checks
