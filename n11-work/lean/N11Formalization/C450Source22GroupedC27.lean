import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((2796209733:ℚ)/5000000000),((6145722311:ℚ)/10000000000),((3436209733:ℚ)/5340000000),((81042945421:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((371941553:ℚ)/500000000),((-1488470949532976671027367137664377:ℚ)/19034163000000000000000000000000000),((-3591083580009258131712311:ℚ)/9728000000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((6069569371:ℚ)/10000000000),((159605811:ℚ)/250000000),((7349569371:ℚ)/11060000000),((697221307:ℚ)/890000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6457850521:ℚ)/10000000000),((-398219169466717789840294595422024948497617756473043853:ℚ)/4227809425000000000000000000000000000000000000000000000),((-127563745914595538076977:ℚ)/346560000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((3154016419:ℚ)/5000000000),((3311337531:ℚ)/5000000000),((3794016419:ℚ)/5720000000),((43144712841:ℚ)/55300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((4622507:ℚ)/7812500),((-55265159601773548402089533327621140279246903653439133:ℚ)/584841400000000000000000000000000000000000000000000000),((-50790660618652053482947607:ℚ)/138624000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((1309286387:ℚ)/2000000000),((3370936571:ℚ)/5000000000),((1565286387:ℚ)/2326000000),((43800302281:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5328306597:ℚ)/10000000000),((-997053740452780447124858210944974376524973989671829:ℚ)/9831485918750000000000000000000000000000000000000000),((-16902327967955445871256189:ℚ)/46208000000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((6665609331:ℚ)/10000000000),((6861056737:ℚ)/10000000000),((7945609331:ℚ)/11820000000),((88911624107:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5011016731:ℚ)/10000000000),((-392216751183313369169847858234987181349513057635382191:ℚ)/3870470081250000000000000000000000000000000000000000000),((-67443302741421631944604901:ℚ)/184832000000000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((3392386457:ℚ)/5000000000),((6980226541:ℚ)/10000000000),((4032386457:ℚ)/6005000000),((90222491951:ℚ)/118200000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2337105417:ℚ)/5000000000),((-68509437017914758943549870734456465536300350060372959:ℚ)/676688906640625000000000000000000000000000000000000000),((-67273516895830405224888749:ℚ)/184832000000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((3451961673:ℚ)/5000000000),((7099383201:ℚ)/10000000000),((4091961673:ℚ)/6100000000),((91533215211:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4313289027:ℚ)/10000000000),((-71736132806741353780720784945728657717588629195580351:ℚ)/709315625000000000000000000000000000000000000000000000),((-201299864119499476660755887:ℚ)/554496000000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((7023061243:ℚ)/10000000000),((7218527327:ℚ)/10000000000),((2767687081:ℚ)/4130000000),((92843800597:ℚ)/122000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((980391433:ℚ)/2500000000),((-5559247270326686971547510264123158777481282120565783:ℚ)/55035153906250000000000000000000000000000000000000000),((-66922616514152109458339941:ℚ)/184832000000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((1785546797:ℚ)/2500000000),((7337659491:ℚ)/10000000000),((2105546797:ℚ)/3145000000),((31384751467:ℚ)/41300000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((436080609:ℚ)/1250000000),((-9576513522683942899805484722475834874313275085771:ℚ)/94931865310668945312500000000000000000000000000000),((-200224507926536761895499047:ℚ)/554496000000000000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((1815325431:ℚ)/2500000000),((3787945023:ℚ)/5000000000),((2135325431:ℚ)/3240000000),((48387395253:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((299668379:ℚ)/1000000000),((-373136657012499130645995765049219886592022713790211:ℚ)/3936600000000000000000000000000000000000000000000000),((-49737997495827773658807023:ℚ)/138624000000000000000000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((7499498589:ℚ)/10000000000),((9480480953:ℚ)/10000000000),((8779498589:ℚ)/16000000000),((117725290483:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1628073601:ℚ)/10000000000),((-84537098591014005324518123034080232944705034972656809:ℚ)/2400000000000000000000000000000000000000000000000000000),((-349314036922314527:ℚ)/972800000000000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((9403877971:ℚ)/10000000000),((6642931163:ℚ)/5000000000),((3561292657:ℚ)/7360000000),((79792242793:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((177205458285711448593961:ℚ)/27084800000000000000000000),((-45991953:ℚ)/128000000)⟩
theorem valid11 : Valid source22 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC27
#check @N11Formalization.C450Source22GroupedC27.bound
#print axioms N11Formalization.C450Source22GroupedC27.valid0
#print axioms N11Formalization.C450Source22GroupedC27.valid1
#print axioms N11Formalization.C450Source22GroupedC27.valid2
#print axioms N11Formalization.C450Source22GroupedC27.valid3
#print axioms N11Formalization.C450Source22GroupedC27.valid4
#print axioms N11Formalization.C450Source22GroupedC27.valid5
#print axioms N11Formalization.C450Source22GroupedC27.valid6
#print axioms N11Formalization.C450Source22GroupedC27.valid7
#print axioms N11Formalization.C450Source22GroupedC27.valid8
#print axioms N11Formalization.C450Source22GroupedC27.valid9
#print axioms N11Formalization.C450Source22GroupedC27.valid10
#print axioms N11Formalization.C450Source22GroupedC27.valid11
#print axioms N11Formalization.C450Source22GroupedC27.bound
#print axioms N11Formalization.C450Source22GroupedC27.endpoint_checks
