import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((318062367:ℚ)/500000000),((6650101893:ℚ)/10000000000),((-15150305679:ℚ)/49600000000),((-215662367:ℚ)/1030000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5790073589:ℚ)/10000000000),((20786472583653817606195118644212504927458124489840947:ℚ)/317573784375000000000000000000000000000000000000000000),((1676384543333605954718239:ℚ)/22179840000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((6599719777:ℚ)/10000000000),((3444290339:ℚ)/5000000000),((-7932871017:ℚ)/25750000000),((-4551719777:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((648577213:ℚ)/1250000000),((51003759855478292479606282893703175417895633909093553127:ℚ)/784207515600000000000000000000000000000000000000000000000),((211106329413223790359751093:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((6838122619:ℚ)/10000000000),((437987141:ℚ)/625000000),((-337987141:ℚ)/1112500000),((-4790122619:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1128982981:ℚ)/2500000000),((181661911604602296887063156418433271693964866051634267123:ℚ)/2857713244175000000000000000000000000000000000000000000000),((198656275305070416679917037:ℚ)/2957312000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((6957300239:ℚ)/10000000000),((3533697493:ℚ)/5000000000),((-8201092479:ℚ)/27175000000),((-2238623:ℚ)/10000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4142107779:ℚ)/10000000000),((53401330537446446198842027751822899860811723977:ℚ)/849218750000000000000000000000000000000000000000),((192416722741105359837430357:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((7016883463:ℚ)/10000000000),((7126991817:ℚ)/10000000000),((-5526991817:ℚ)/18275000000),((-4968883463:ℚ)/22120000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((985695101:ℚ)/2500000000),((72812624884922127387919024873876744370013695148235783927:ℚ)/1158948258628125000000000000000000000000000000000000000000),((189293297816029784149887973:ℚ)/2957312000000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((7076463091:ℚ)/10000000000),((449161553:ℚ)/625000000),((-1047484659:ℚ)/3456250000),((-5028463091:ℚ)/22310000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((373342159:ℚ)/1000000000),((776157001695832239057608272766927018751893511052057803:ℚ)/12364659093554687500000000000000000000000000000000000000),((186167434400672048256550077:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((446002451:ℚ)/625000000),((7246174177:ℚ)/10000000000),((-16938522531:ℚ)/55775000000),((-106000817:ℚ)/468750000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((439029179:ℚ)/1250000000),((527789957466090871188142275044846385476083573310917:ℚ)/8415011689066886901855468750000000000000000000000000),((714996594083049127509117:ℚ)/11552000000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((7195611927:ℚ)/10000000000),((7305759897:ℚ)/10000000000),((-5705759897:ℚ)/18750000000),((-5147611927:ℚ)/22690000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((409602073:ℚ)/1250000000),((5719427951320170116536083482149789423741172248126231:ℚ)/91262743039062500000000000000000000000000000000000000),((539725123961691973956796879:ℚ)/8871936000000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((725518131:ℚ)/1000000000),((73653421:ℚ)/100000000),((-172960263:ℚ)/567250000),((-520718131:ℚ)/2288000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1511922269:ℚ)/5000000000),((5318358331565059802443668492966740321053026692171855967:ℚ)/84928328742400000000000000000000000000000000000000000000),((5303255100984666434365111:ℚ)/88719360000000000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((146294949:ℚ)/200000000),((7484496297:ℚ)/10000000000),((-17653488891:ℚ)/57200000000),((-105334949:ℚ)/465200000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2748468651:ℚ)/10000000000),((218323025569457845678747384318404222309411249938463:ℚ)/3460683043400000000000000000000000000000000000000000),((208367412222899026172551:ℚ)/3548774400000000000000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((7433870317:ℚ)/10000000000),((1900909359:ℚ)/2500000000),((-4502728077:ℚ)/14537500000),((-5385870317:ℚ)/23640000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2094720677:ℚ)/10000000000),((28002738889871154570326398165391267439173265472242998061:ℚ)/444578439950000000000000000000000000000000000000000000000),((167360809859455116115622013:ℚ)/2957312000000000000000000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((7552981143:ℚ)/10000000000),((7841882993:ℚ)/10000000000),((-6241882993:ℚ)/19700000000),((-5504981143:ℚ)/24400000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1112931397:ℚ)/10000000000),((1713071579246710479694384416178334525596750929565449385841:ℚ)/26829154200000000000000000000000000000000000000000000000000),((483216733576449309475873999:ℚ)/8871936000000000000000000000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((7791168931:ℚ)/10000000000),((4159121193:ℚ)/5000000000),((-10077363579:ℚ)/30500000000),((-5743168931:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((72377552519954229410036397715045321478838242813697335021:ℚ)/1106531020800000000000000000000000000000000000000000000000),((54912379:ℚ)/1024000000)⟩
theorem valid12 : Valid source17 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((1033427879:ℚ)/1250000000),((10222384487:ℚ)/10000000000),((-8622384487:ℚ)/21600000000),((-777427879:ℚ)/4000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((44183937823079433552933231037181113913151869745015301:ℚ)/600000000000000000000000000000000000000000000000000000),((54912379:ℚ)/1024000000)⟩
theorem valid13 : Valid source17 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((5085622299:ℚ)/5000000000),((14027240481:ℚ)/10000000000),((-37281721443:ℚ)/80000000000),((-4061622299:ℚ)/22080000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2114079314238746378774505112894310492086995316749814721:ℚ)/25229491200000000000000000000000000000000000000000000000),((54912379:ℚ)/1024000000)⟩
theorem valid14 : Valid source17 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source17 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC11
#check @N11Formalization.C450Source17GroupedC11.bound
#print axioms N11Formalization.C450Source17GroupedC11.valid0
#print axioms N11Formalization.C450Source17GroupedC11.valid1
#print axioms N11Formalization.C450Source17GroupedC11.valid2
#print axioms N11Formalization.C450Source17GroupedC11.valid3
#print axioms N11Formalization.C450Source17GroupedC11.valid4
#print axioms N11Formalization.C450Source17GroupedC11.valid5
#print axioms N11Formalization.C450Source17GroupedC11.valid6
#print axioms N11Formalization.C450Source17GroupedC11.valid7
#print axioms N11Formalization.C450Source17GroupedC11.valid8
#print axioms N11Formalization.C450Source17GroupedC11.valid9
#print axioms N11Formalization.C450Source17GroupedC11.valid10
#print axioms N11Formalization.C450Source17GroupedC11.valid11
#print axioms N11Formalization.C450Source17GroupedC11.valid12
#print axioms N11Formalization.C450Source17GroupedC11.valid13
#print axioms N11Formalization.C450Source17GroupedC11.valid14
#print axioms N11Formalization.C450Source17GroupedC11.bound
#print axioms N11Formalization.C450Source17GroupedC11.endpoint_checks
