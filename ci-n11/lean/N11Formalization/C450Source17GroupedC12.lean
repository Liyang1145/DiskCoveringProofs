import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((6322722249:ℚ)/10000000000),((6608728913:ℚ)/10000000000),((-4688728913:ℚ)/19840000000),((-3762722249:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((73525821:ℚ)/125000000),((322891372930436894823371116633332030678344563071507377381:ℚ)/4962090380859375000000000000000000000000000000000000000000),((23983077001532661243120883:ℚ)/693120000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((410077051:ℚ)/625000000),((1711814239:ℚ)/2500000000),((-1231814239:ℚ)/5150000000),((-83359017:ℚ)/556250000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5289842769:ℚ)/10000000000),((894237638489705575635999053905634152683879457639247:ℚ)/13849603080749511718750000000000000000000000000000000),((27084934641147137332811:ℚ)/902500000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((3399835521:ℚ)/5000000000),((1393298771:ℚ)/2000000000),((-1009298771:ℚ)/4272000000),((-2119835521:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((463051639:ℚ)/1000000000),((44158239829787334251431123977114668467467957479108785617:ℚ)/697683897503662109375000000000000000000000000000000000000),((4403008149933467640108403:ℚ)/173280000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((6918865417:ℚ)/10000000000),((7085713927:ℚ)/10000000000),((-5165713927:ℚ)/21740000000),((-4358865417:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1066504987:ℚ)/2500000000),((70818655516584561434215092197146730132095235633690554647:ℚ)/1121979698480224609375000000000000000000000000000000000000),((5338216020208613111429329:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((7038044441:ℚ)/10000000000),((7145317923:ℚ)/10000000000),((-746473989:ℚ)/3160000000),((-4478044441:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1934827533:ℚ)/5000000000),((215797873599647171691434260406619138306985832281011279:ℚ)/3449960684585571289062500000000000000000000000000000000),((4805130686421058228032241:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((7097628443:ℚ)/10000000000),((7204918029:ℚ)/10000000000),((-5284918029:ℚ)/22310000000),((-4537628443:ℚ)/28125000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3656306111:ℚ)/10000000000),((113567347452470138884893811136408969187928134531082576463:ℚ)/1817642524838447570800781250000000000000000000000000000000),((4538353065771067520875289:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((7157208897:ℚ)/10000000000),((1452902869:ℚ)/2000000000),((-1068902869:ℚ)/4500000000),((-4597208897:ℚ)/28362500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((137214213:ℚ)/400000000),((11125011225570456462750243279850562266544101571043761:ℚ)/178247544998168945312500000000000000000000000000000000),((12814254870762330353119747:ℚ)/693120000000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((7216785893:ℚ)/10000000000),((1831026741:ℚ)/2500000000),((-1351026741:ℚ)/5672500000),((-4656785893:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3189120431:ℚ)/10000000000),((10342147004110851225109172989915449071036841293368373489609:ℚ)/165875642075000000000000000000000000000000000000000000000000),((4004325987169083957750489:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((7276359517:ℚ)/10000000000),((186082037:ℚ)/250000000),((-138082037:ℚ)/572000000),((-4716359517:ℚ)/29075000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((732205493:ℚ)/2500000000),((52955265099414606441672366562000139167583092796291084631:ℚ)/844893321142578125000000000000000000000000000000000000000),((3737075800717648848342729:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((7395496983:ℚ)/10000000000),((7562442277:ℚ)/10000000000),((-5642442277:ℚ)/23260000000),((-4835496983:ℚ)/29550000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2325073817:ℚ)/10000000000),((54315331446443206707430844205198940024843751884111054639:ℚ)/868317265527343750000000000000000000000000000000000000000),((9606301183356758454435187:ℚ)/693120000000000000000000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((7514621933:ℚ)/10000000000),((7800725297:ℚ)/10000000000),((-5880725297:ℚ)/23640000000),((-4954621933:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((300067367:ℚ)/2000000000),((3310147294692942882236010744756860165592595973016975975731:ℚ)/52400691796875000000000000000000000000000000000000000000000),((2666489430190993817997929:ℚ)/231040000000000000000000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((7752836639:ℚ)/10000000000),((4138576483:ℚ)/5000000000),((-3178576483:ℚ)/12200000000),((-5192836639:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((138955935793659544087112702854206163550657186504695734889:ℚ)/2161193400000000000000000000000000000000000000000000000000),((1264369:ℚ)/128000000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((8229139803:ℚ)/10000000000),((2036300579:ℚ)/2000000000),((-1652300579:ℚ)/5184000000),((-5669139803:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((42374020033493679143453359934285636149550798156026773193:ℚ)/600000000000000000000000000000000000000000000000000000000),((1264369:ℚ)/128000000)⟩
theorem valid12 : Valid source17 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((2026622147:ℚ)/2000000000),((6993301097:ℚ)/5000000000),((-6033301097:ℚ)/16000000000),((-504874049:ℚ)/3680000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((9301901377884853778326425051162814916170228304016971:ℚ)/116803200000000000000000000000000000000000000000000000),((1264369:ℚ)/128000000)⟩
theorem valid13 : Valid source17 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source17 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source17 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2269:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source17 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source17 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC12
#check @N11Formalization.C450Source17GroupedC12.bound
#print axioms N11Formalization.C450Source17GroupedC12.valid0
#print axioms N11Formalization.C450Source17GroupedC12.valid1
#print axioms N11Formalization.C450Source17GroupedC12.valid2
#print axioms N11Formalization.C450Source17GroupedC12.valid3
#print axioms N11Formalization.C450Source17GroupedC12.valid4
#print axioms N11Formalization.C450Source17GroupedC12.valid5
#print axioms N11Formalization.C450Source17GroupedC12.valid6
#print axioms N11Formalization.C450Source17GroupedC12.valid7
#print axioms N11Formalization.C450Source17GroupedC12.valid8
#print axioms N11Formalization.C450Source17GroupedC12.valid9
#print axioms N11Formalization.C450Source17GroupedC12.valid10
#print axioms N11Formalization.C450Source17GroupedC12.valid11
#print axioms N11Formalization.C450Source17GroupedC12.valid12
#print axioms N11Formalization.C450Source17GroupedC12.valid13
#print axioms N11Formalization.C450Source17GroupedC12.bound
#print axioms N11Formalization.C450Source17GroupedC12.endpoint_checks
