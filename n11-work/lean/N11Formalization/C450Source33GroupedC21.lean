import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/4),((5:ℚ)/16),((11092979:ℚ)/19531250),((6014547911:ℚ)/10000000000),((83121916:ℚ)/201171875),((10110547911:ℚ)/19840000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7267820707:ℚ)/10000000000),((-1047467014181384279018600940431929466638824888614599766401:ℚ)/3845620045166015625000000000000000000000000000000000000000),((-1013480041820717899059627127:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((5921630029:ℚ)/10000000000),((625613471:ℚ)/1000000000),((10881630029:ℚ)/26700000000),((1035213471:ℚ)/2060000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((6774687701:ℚ)/10000000000),((-8426622064531182650182211210024315544254597863266778243493:ℚ)/31552099260468750000000000000000000000000000000000000000000),((-10167867059871494371688167:ℚ)/29573120000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((6163324231:ℚ)/10000000000),((6376818309:ℚ)/10000000000),((11123324231:ℚ)/27175000000),((10472818309:ℚ)/21360000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((781248729:ℚ)/1250000000),((-79641946418462536766051442286873135409455889508318117725069:ℚ)/298050561013564453125000000000000000000000000000000000000000),((-1030216830938588430773920847:ℚ)/2957312000000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((251362343:ℚ)/400000000),((6497433899:ℚ)/10000000000),((449762343:ℚ)/1106000000),((10593433899:ℚ)/21740000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((5973130277:ℚ)/10000000000),((-590633509575579604432093262134037444691282543377778273:ℚ)/2230110961824921875000000000000000000000000000000000000),((-1031344207442654303181917487:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((3202361541:ℚ)/5000000000),((827248129:ℚ)/1250000000),((5682361541:ℚ)/14062500000),((1339248129:ℚ)/2765000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1136935933:ℚ)/2000000000),((-20704767021073408072854299407796839838819100572291261609:ℚ)/78844623640179634094238281250000000000000000000000000000),((-16129146431745154761441767:ℚ)/46208000000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((3262660701:ℚ)/5000000000),((1347695003:ℚ)/2000000000),((5742660701:ℚ)/14300000000),((2166895003:ℚ)/4500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1345684419:ℚ)/2500000000),((-12853368845367578468019221370202337191880441759128754311:ℚ)/49345993125000000000000000000000000000000000000000000000),((-41319228128835855652304783:ℚ)/118292480000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((830732117:ℚ)/1250000000),((1714726733:ℚ)/2500000000),((1450732117:ℚ)/3634375000),((2738726733:ℚ)/5720000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1266213509:ℚ)/2500000000),((-317144289015699227522140601827527383941776015577937926903:ℚ)/1227075534378166198730468750000000000000000000000000000000),((-64593159746166294941630143:ℚ)/184832000000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((6766332851:ℚ)/10000000000),((6979283661:ℚ)/10000000000),((3908777617:ℚ)/9850000000),((11075283661:ℚ)/23260000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2363887557:ℚ)/5000000000),((-51813371957368482886478739496083366065774796414394788262001:ℚ)/201970595961660156250000000000000000000000000000000000000000),((-54410276803944392052170533:ℚ)/155648000000000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((6886752103:ℚ)/10000000000),((360994107:ℚ)/500000000),((11846752103:ℚ)/30500000000),((565794107:ℚ)/1182000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4367017547:ℚ)/10000000000),((-517575065643097791866133881691754913987106327815164460115077:ℚ)/2064587256796875000000000000000000000000000000000000000000000),((-2554366017410635340042063:ℚ)/7393280000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((3563715749:ℚ)/5000000000),((770052433:ℚ)/1000000000),((6043715749:ℚ)/16200000000),((1179652433:ℚ)/2440000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((354500671:ℚ)/1000000000),((-792227943904360938864541069824185524226477782951699333519:ℚ)/3295819935000000000000000000000000000000000000000000000000),((-33095147815581211:ℚ)/97280000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((3804110387:ℚ)/5000000000),((9617663373:ℚ)/10000000000),((6284110387:ℚ)/20000000000),((13713663373:ℚ)/25920000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-744847672284829137988084680790981815028724522956687434451:ℚ)/3645000000000000000000000000000000000000000000000000000000),((-364743329:ℚ)/1024000000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((9525804751:ℚ)/10000000000),((13437672533:ℚ)/10000000000),((14485804751:ℚ)/55200000000),((17533672533:ℚ)/32000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-13666320888500835326608813481553900803126866121123760389:ℚ)/78842160000000000000000000000000000000000000000000000000),((-364743329:ℚ)/1024000000)⟩
theorem valid11 : Valid source33 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC21
#check @N11Formalization.C450Source33GroupedC21.bound
#print axioms N11Formalization.C450Source33GroupedC21.valid0
#print axioms N11Formalization.C450Source33GroupedC21.valid1
#print axioms N11Formalization.C450Source33GroupedC21.valid2
#print axioms N11Formalization.C450Source33GroupedC21.valid3
#print axioms N11Formalization.C450Source33GroupedC21.valid4
#print axioms N11Formalization.C450Source33GroupedC21.valid5
#print axioms N11Formalization.C450Source33GroupedC21.valid6
#print axioms N11Formalization.C450Source33GroupedC21.valid7
#print axioms N11Formalization.C450Source33GroupedC21.valid8
#print axioms N11Formalization.C450Source33GroupedC21.valid9
#print axioms N11Formalization.C450Source33GroupedC21.valid10
#print axioms N11Formalization.C450Source33GroupedC21.valid11
#print axioms N11Formalization.C450Source33GroupedC21.bound
#print axioms N11Formalization.C450Source33GroupedC21.endpoint_checks
