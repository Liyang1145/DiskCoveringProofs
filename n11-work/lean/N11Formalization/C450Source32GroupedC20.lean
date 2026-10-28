import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/16),((1:ℚ)/4),((5772639227:ℚ)/10000000000),((3051833709:ℚ)/5000000000),((36517917681:ℚ)/103000000000),((5531833709:ℚ)/12400000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3540816703:ℚ)/5000000000),((-298718222202446799912107381724965495001786190041547161693:ℚ)/1365908750000000000000000000000000000000000000000000000000),((-27606741760616518690072123:ℚ)/86640000000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((3007273953:ℚ)/5000000000),((6345102741:ℚ)/10000000000),((6207273953:ℚ)/17800000000),((11305102741:ℚ)/25750000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((657720329:ℚ)/1000000000),((-376493993579787638254960715518230653135392834717919101:ℚ)/1762422500000000000000000000000000000000000000000000000),((-111498732269662436813873323:ℚ)/346560000000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((1251226941:ℚ)/2000000000),((6465714767:ℚ)/10000000000),((7593680823:ℚ)/21740000000),((3808571589:ℚ)/8900000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((6038147959:ℚ)/10000000000),((-2737598566029424190219881703575735049676268543690686771:ℚ)/12843655030000000000000000000000000000000000000000000000),((-37853302975417357097500129:ℚ)/115520000000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((49818893:ℚ)/78125000),((3293130679:ℚ)/5000000000),((299456679:ℚ)/864062500),((5773130679:ℚ)/13587500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1438130871:ℚ)/2500000000),((-379595876166062698045115495735834856915901076769:ℚ)/1799979135394096374511718750000000000000000000000),((-9503690295755044094930001:ℚ)/28880000000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((3248716947:ℚ)/5000000000),((6706745927:ℚ)/10000000000),((6448716947:ℚ)/18750000000),((11666745927:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5453890949:ℚ)/10000000000),((-20156069016353594824205340517832270701851382051972957:ℚ)/96559524536132812500000000000000000000000000000000000),((-38169525321908110166987569:ℚ)/115520000000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((6617985027:ℚ)/10000000000),((3413585827:ℚ)/5000000000),((39053955081:ℚ)/114400000000),((1964528609:ℚ)/4687500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((256997273:ℚ)/500000000),((-386840257224155088134429862966814715510690962011551428533:ℚ)/1871492480000000000000000000000000000000000000000000000000),((-9579402741627099592148169:ℚ)/28880000000000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((673847501:ℚ)/1000000000),((3473770751:ℚ)/5000000000),((3941542503:ℚ)/11630000000),((5953770751:ℚ)/14300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4807648997:ℚ)/10000000000),((-402619216558474472241626853704281747969648739040737979:ℚ)/1966297183750000000000000000000000000000000000000000000),((-9614758155819183098450561:ℚ)/28880000000000000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((6858906927:ℚ)/10000000000),((3533929119:ℚ)/5000000000),((13258906927:ℚ)/39400000000),((6013929119:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4452854523:ℚ)/10000000000),((-3878357532860429854307556193199223453807262303233491499:ℚ)/19113432500000000000000000000000000000000000000000000000),((-28945352863416347851696963:ℚ)/86640000000000000000000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((872410457:ℚ)/1250000000),((3654171277:ℚ)/5000000000),((5017231371:ℚ)/15250000000),((2044723759:ℚ)/4925000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((203481969:ℚ)/500000000),((-876987079339054001187309528083696783218634536333797663:ℚ)/4433222656250000000000000000000000000000000000000000000),((-9581683113679836760092969:ℚ)/28880000000000000000000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((1443976427:ℚ)/2000000000),((3894388601:ℚ)/5000000000),((2723976427:ℚ)/8640000000),((6374388601:ℚ)/15250000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((3176100929:ℚ)/10000000000),((-50749380441372539184194226766077063165434820095722133:ℚ)/268738560000000000000000000000000000000000000000000000),((-2019679288459149:ℚ)/6080000000000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((308020973:ℚ)/400000000),((4852644133:ℚ)/5000000000),((1692062919:ℚ)/6400000000),((814738237:ℚ)/1800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-52019774985912311575453267609901847475356686164407387:ℚ)/327680000000000000000000000000000000000000000000000000),((-5541033:ℚ)/16000000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((1202207921:ℚ)/1250000000),((6762284089:ℚ)/5000000000),((2002207921:ℚ)/9200000000),((9242284089:ℚ)/20000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-95999473669577057831623384970645129733134025469039439:ℚ)/730020000000000000000000000000000000000000000000000000),((-5541033:ℚ)/16000000)⟩
theorem valid11 : Valid source32 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC20
#check @N11Formalization.C450Source32GroupedC20.bound
#print axioms N11Formalization.C450Source32GroupedC20.valid0
#print axioms N11Formalization.C450Source32GroupedC20.valid1
#print axioms N11Formalization.C450Source32GroupedC20.valid2
#print axioms N11Formalization.C450Source32GroupedC20.valid3
#print axioms N11Formalization.C450Source32GroupedC20.valid4
#print axioms N11Formalization.C450Source32GroupedC20.valid5
#print axioms N11Formalization.C450Source32GroupedC20.valid6
#print axioms N11Formalization.C450Source32GroupedC20.valid7
#print axioms N11Formalization.C450Source32GroupedC20.valid8
#print axioms N11Formalization.C450Source32GroupedC20.valid9
#print axioms N11Formalization.C450Source32GroupedC20.valid10
#print axioms N11Formalization.C450Source32GroupedC20.valid11
#print axioms N11Formalization.C450Source32GroupedC20.bound
#print axioms N11Formalization.C450Source32GroupedC20.endpoint_checks
