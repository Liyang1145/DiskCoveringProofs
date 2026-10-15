import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/8),((-1:ℚ)/16),((24162189:ℚ)/39062500),((648745881:ℚ)/1000000000),((87254119:ℚ)/5150000000),((35837811:ℚ)/387500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((774987513:ℚ)/1250000000),((27160443765151946130557291348544653:ℚ)/154322616699218750000000000000000000),((-32128498493040619950641:ℚ)/135375000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((6425799731:ℚ)/10000000000),((840911921:ℚ)/1250000000),((26362693:ℚ)/2225000000),((8934200269:ℚ)/103000000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((2816477733:ℚ)/5000000000),((36807323984701589678516681639115969856275070858337152895201:ℚ)/211315687670898437500000000000000000000000000000000000000000),((-739810418506764390911185527:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((3332939031:ℚ)/5000000000),((6847151521:ℚ)/10000000000),((512848479:ℚ)/54350000000),((1449020323:ℚ)/17800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((501028063:ℚ)/1000000000),((7158145981312290255583358837393938777041153115498403882970143:ℚ)/41648475818050000000000000000000000000000000000000000000000000),((-583365296980826259240235181:ℚ)/2217984000000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((6785848573:ℚ)/10000000000),((3483484577:ℚ)/5000000000),((2487537:ℚ)/350000000),((8574151427:ℚ)/108700000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4671068741:ℚ)/10000000000),((601539131915655460853008581981956468188214548805085120529:ℚ)/3511936922265625000000000000000000000000000000000000000000),((-796847876534699509254385303:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((1726444131:ℚ)/2500000000),((3543375127:ℚ)/5000000000),((136624873:ℚ)/28125000000),((2113555869:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2153726473:ℚ)/5000000000),((261068222680204886785803750166220117469716256646914953663:ℚ)/1528806086718750000000000000000000000000000000000000000000),((-152979530187109523129285381:ℚ)/554496000000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((439104007:ℚ)/625000000),((7206496671:ℚ)/10000000000),((153503329:ℚ)/57200000000),((520895993:ℚ)/7031250000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3912594757:ℚ)/10000000000),((2522163673846933991272050502202744037060508542348813225479:ℚ)/14809092879295349121093750000000000000000000000000000000000),((-3261521778030559472703343:ℚ)/11552000000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((1786378347:ℚ)/2500000000),((3663105067:ℚ)/5000000000),((16894933:ℚ)/29075000000),((2053621653:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3475818911:ℚ)/10000000000),((8400692143952052897760608948532178384173978754069929844463153:ℚ)/49439896722287500000000000000000000000000000000000000000000000),((-443572242000510108451949:ℚ)/1536000000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((7265326261:ℚ)/10000000000),((7445900121:ℚ)/10000000000),((-85900121:ℚ)/58150000000),((8094673739:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1489346557:ℚ)/5000000000),((416825012005467778110100101279312592175613063811785546391:ℚ)/2457871479687500000000000000000000000000000000000000000000),((-873115655014759688673799847:ℚ)/2957312000000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((7385104519:ℚ)/10000000000),((960659699:ℚ)/1250000000),((-13553233:ℚ)/2462500000),((7974895481:ℚ)/118200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1191847053:ℚ)/5000000000),((1755006860770299880734253263938817003851548167600126470461:ℚ)/10321253550000000000000000000000000000000000000000000000000),((-892223535613455349324028527:ℚ)/2957312000000000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((1524912753:ℚ)/2000000000),((510237817:ℚ)/625000000),((-50237817:ℚ)/3812500000),((1547087247:ℚ)/24400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((3881819241655760028901962518512874397676640779333098883:ℚ)/22698100000000000000000000000000000000000000000000000000),((-320831281:ℚ)/1024000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((1620626743:ℚ)/2000000000),((10074536657:ℚ)/10000000000),((-2714536657:ℚ)/64800000000),((1451373257:ℚ)/25920000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1214280389604028163502383172041848596896268268059125197:ℚ)/6802444800000000000000000000000000000000000000000000000),((-320831281:ℚ)/1024000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((10013994171:ℚ)/10000000000),((13887091199:ℚ)/10000000000),((-6527091199:ℚ)/80000000000),((5346005829:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((206596310587992770869386441227703642923:ℚ)/1024000000000000000000000000000000000000),((-320831281:ℚ)/1024000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC15
#check @N11Formalization.C450Source25GroupedC15.bound
#print axioms N11Formalization.C450Source25GroupedC15.valid0
#print axioms N11Formalization.C450Source25GroupedC15.valid1
#print axioms N11Formalization.C450Source25GroupedC15.valid2
#print axioms N11Formalization.C450Source25GroupedC15.valid3
#print axioms N11Formalization.C450Source25GroupedC15.valid4
#print axioms N11Formalization.C450Source25GroupedC15.valid5
#print axioms N11Formalization.C450Source25GroupedC15.valid6
#print axioms N11Formalization.C450Source25GroupedC15.valid7
#print axioms N11Formalization.C450Source25GroupedC15.valid8
#print axioms N11Formalization.C450Source25GroupedC15.valid9
#print axioms N11Formalization.C450Source25GroupedC15.valid10
#print axioms N11Formalization.C450Source25GroupedC15.valid11
#print axioms N11Formalization.C450Source25GroupedC15.bound
#print axioms N11Formalization.C450Source25GroupedC15.endpoint_checks
