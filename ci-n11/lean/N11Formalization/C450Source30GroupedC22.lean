import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((5:ℚ)/16),((3:ℚ)/8),((5671031851:ℚ)/10000000000),((599897679:ℚ)/1000000000),((9255031851:ℚ)/20600000000),((2727693037:ℚ)/4960000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((72847817:ℚ)/100000000),((-55776819744479915146662645791544057457520087923979856417:ℚ)/260998374400000000000000000000000000000000000000000000000),((-1346554946511079490803689:ℚ)/3696640000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((5912049017:ℚ)/10000000000),((1559917013:ℚ)/2500000000),((9496049017:ℚ)/21360000000),((6999751039:ℚ)/12875000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((6794774533:ℚ)/10000000000),((-118588171603985479634585069320904692315522625278022689:ℚ)/563975200000000000000000000000000000000000000000000000),((-8427678017306809675238401:ℚ)/23104000000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((6152810711:ℚ)/10000000000),((6359928397:ℚ)/10000000000),((9736810711:ℚ)/21740000000),((28359785191:ℚ)/53400000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1254718897:ℚ)/2000000000),((-13594148854134990591773343902830517876005819767875736461:ℚ)/64218275150000000000000000000000000000000000000000000000),((-136315318196793355419794161:ℚ)/369664000000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((3136552177:ℚ)/5000000000),((6480135891:ℚ)/10000000000),((4928552177:ℚ)/11060000000),((28720407673:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1499677409:ℚ)/2500000000),((-27757902230140799470235877601618839277256516759541187:ℚ)/132119044531250000000000000000000000000000000000000000),((-136342885056170313569712049:ℚ)/369664000000000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/16),((3:ℚ)/8),((6393343959:ℚ)/10000000000),((3300146637:ℚ)/5000000000),((9977343959:ℚ)/22500000000),((14540439911:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5712431741:ℚ)/10000000000),((-2148329802778968648317122012906285548726017609860847:ℚ)/10299682617187500000000000000000000000000000000000000),((-34086096879681815092898801:ℚ)/92416000000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((6513532329:ℚ)/10000000000),((6720403103:ℚ)/10000000000),((10097532329:ℚ)/22880000000),((29441209309:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5412919507:ℚ)/10000000000),((-15506127335206007992420171957084689034044005467204970059:ℚ)/74859699200000000000000000000000000000000000000000000000),((-136319860196203303066425161:ℚ)/369664000000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((6633672079:ℚ)/10000000000),((6840467759:ℚ)/10000000000),((10217672079:ℚ)/23260000000),((29801403277:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((637225759:ℚ)/1250000000),((-16183013179704264968232611548335722809999217642136626061:ℚ)/78651887350000000000000000000000000000000000000000000000),((-136269335428235219802039849:ℚ)/369664000000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((6753765647:ℚ)/10000000000),((696048947:ℚ)/1000000000),((10337765647:ℚ)/23640000000),((3016146841:ℚ)/5815000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((595495099:ℚ)/1250000000),((-468896326248772285094729544496493377696575020186324717:ℚ)/2293611900000000000000000000000000000000000000000000000),((-1361928433160006572350961:ℚ)/3696640000000000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((1718453827:ℚ)/2500000000),((7200412243:ℚ)/10000000000),((2614453827:ℚ)/6100000000),((30881236729:ℚ)/59100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4407091459:ℚ)/10000000000),((-282770947313579534111886608283944163256462758387447993:ℚ)/1418631250000000000000000000000000000000000000000000000),((-134548016309694373654815921:ℚ)/369664000000000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((7113791291:ℚ)/10000000000),((3839912827:ℚ)/5000000000),((10697791291:ℚ)/25920000000),((16159738481:ℚ)/30500000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((3596354877:ℚ)/10000000000),((-85194750726138535174210575074253445704174515008168267:ℚ)/447897600000000000000000000000000000000000000000000000),((-43437568359464053:ℚ)/121600000000000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((7593301499:ℚ)/10000000000),((479662197:ℚ)/500000000),((11177301499:ℚ)/32000000000),((1902986591:ℚ)/3240000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((419883609:ℚ)/10000000000),((-31948967801359262500038021018276371645990829110939648009:ℚ)/204800000000000000000000000000000000000000000000000000000),((-45296141773998517:ℚ)/121600000000000000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((2376753281:ℚ)/2500000000),((13408928013:ℚ)/10000000000),((3272753281:ℚ)/11040000000),((49506784039:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-9790960356166018257151651187010337700046281434129393:ℚ)/77868800000000000000000000000000000000000000000000000),((-47707479:ℚ)/128000000)⟩
theorem valid11 : Valid source30 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC22
#check @N11Formalization.C450Source30GroupedC22.bound
#print axioms N11Formalization.C450Source30GroupedC22.valid0
#print axioms N11Formalization.C450Source30GroupedC22.valid1
#print axioms N11Formalization.C450Source30GroupedC22.valid2
#print axioms N11Formalization.C450Source30GroupedC22.valid3
#print axioms N11Formalization.C450Source30GroupedC22.valid4
#print axioms N11Formalization.C450Source30GroupedC22.valid5
#print axioms N11Formalization.C450Source30GroupedC22.valid6
#print axioms N11Formalization.C450Source30GroupedC22.valid7
#print axioms N11Formalization.C450Source30GroupedC22.valid8
#print axioms N11Formalization.C450Source30GroupedC22.valid9
#print axioms N11Formalization.C450Source30GroupedC22.valid10
#print axioms N11Formalization.C450Source30GroupedC22.valid11
#print axioms N11Formalization.C450Source30GroupedC22.bound
#print axioms N11Formalization.C450Source30GroupedC22.endpoint_checks
