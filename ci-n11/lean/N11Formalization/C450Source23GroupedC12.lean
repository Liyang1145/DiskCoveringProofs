import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((6356421721:ℚ)/10000000000),((6657995479:ℚ)/10000000000),((-3969995479:ℚ)/19840000000),((-2836421721:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5801667069:ℚ)/10000000000),((151045793902540328517572941887910027104490785917058828863:ℚ)/827015063476562500000000000000000000000000000000000000000),((-1899479104940720692260029:ℚ)/28880000000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((3297957337:ℚ)/5000000000),((1379490091:ℚ)/2000000000),((-841890091:ℚ)/4120000000),((-1537957337:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((649838147:ℚ)/1250000000),((5787293385520615241528135229400615550618890190921369149:ℚ)/31909485498046875000000000000000000000000000000000000000),((-555201821184402489612761:ℚ)/7220000000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((6835264143:ℚ)/10000000000),((7017126081:ℚ)/10000000000),((-1443042027:ℚ)/7120000000),((-3315264143:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((28278393:ℚ)/62500000),((497396894854976962693260430990256360944547561109341671959:ℚ)/2790735590014648437500000000000000000000000000000000000000),((-7633187663178649480921943:ℚ)/86640000000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((3477444923:ℚ)/5000000000),((1427353909:ℚ)/2000000000),((-889753909:ℚ)/4348000000),((-1717444923:ℚ)/13825000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4149981041:ℚ)/10000000000),((12468279281405418964082162050673156256378686485386430133:ℚ)/70123731155014038085937500000000000000000000000000000000),((-1874683500091384875841:ℚ)/20000000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((3537242569:ℚ)/5000000000),((7196579737:ℚ)/10000000000),((-4508579737:ℚ)/22120000000),((-1777242569:ℚ)/13943750000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1870275361:ℚ)/5000000000),((25827866903493121108246594119929104577151472412365356769:ℚ)/146407706552100181579589843750000000000000000000000000000),((-717565256791944890294009:ℚ)/7220000000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((3567135937:ℚ)/5000000000),((7256382499:ℚ)/10000000000),((-4568382499:ℚ)/22310000000),((-1807135937:ℚ)/14062500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3518986321:ℚ)/10000000000),((6673806240325221419552721863093373967572391867573857839:ℚ)/37867552600800991058349609375000000000000000000000000000),((-738021174276064262124361:ℚ)/7220000000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((7025441:ℚ)/9765625),((3687983243:ℚ)/5000000000),((-2343983243:ℚ)/11250000000),((-7175882:ℚ)/55859375),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3283189637:ℚ)/10000000000),((78908629998301739027606355289392159010028497747:ℚ)/445643998682498931884765625000000000000000000000),((-370367642534727243317:ℚ)/3525390625000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((7313590639:ℚ)/10000000000),((1499104589:ℚ)/2000000000),((-961504589:ℚ)/4576000000),((-3793590639:ℚ)/29075000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1377035747:ℚ)/5000000000),((970684798301884393465594590242504099101205773774848247369:ℚ)/5491806587426757812500000000000000000000000000000000000000),((-3198416636992163339277149:ℚ)/28880000000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((7433103663:ℚ)/10000000000),((7615053221:ℚ)/10000000000),((-4927053221:ℚ)/23260000000),((-3913103663:ℚ)/29550000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2099566257:ℚ)/10000000000),((76615600610660781900926604441467049501201695373979133039:ℚ)/434158632763671875000000000000000000000000000000000000000),((-10090071645503029296677783:ℚ)/86640000000000000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((7552591927:ℚ)/10000000000),((7854040179:ℚ)/10000000000),((-1722013393:ℚ)/7880000000),((-4032591927:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((223506607:ℚ)/2000000000),((1555072571601576473997768073139944266224881728365082386803:ℚ)/8733448632812500000000000000000000000000000000000000000000),((-3528874826535263140786701:ℚ)/28880000000000000000000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((389574943:ℚ)/500000000),((4165875139:ℚ)/5000000000),((-2821875139:ℚ)/12200000000),((-213574943:ℚ)/1620000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((8151780376619590865656516454020763239134696453729019:ℚ)/45024862500000000000000000000000000000000000000000000),((-7966127:ℚ)/64000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((4134531609:ℚ)/5000000000),((5120000001:ℚ)/5000000000),((-1258666667:ℚ)/4320000000),((-2374531609:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((66934392274136409199833826309860581653097499388915347179:ℚ)/337500000000000000000000000000000000000000000000000000000),((-7966127:ℚ)/64000000)⟩
theorem valid11 : Valid source23 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((5088435059:ℚ)/5000000000),((35124147:ℚ)/25000000),((-28404147:ℚ)/80000000),((-1109478353:ℚ)/9200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((68266514050879399928084573452140461631453727818947281:ℚ)/304175000000000000000000000000000000000000000000000000),((-7966127:ℚ)/64000000)⟩
theorem valid12 : Valid source23 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC12
#check @N11Formalization.C450Source23GroupedC12.bound
#print axioms N11Formalization.C450Source23GroupedC12.valid0
#print axioms N11Formalization.C450Source23GroupedC12.valid1
#print axioms N11Formalization.C450Source23GroupedC12.valid2
#print axioms N11Formalization.C450Source23GroupedC12.valid3
#print axioms N11Formalization.C450Source23GroupedC12.valid4
#print axioms N11Formalization.C450Source23GroupedC12.valid5
#print axioms N11Formalization.C450Source23GroupedC12.valid6
#print axioms N11Formalization.C450Source23GroupedC12.valid7
#print axioms N11Formalization.C450Source23GroupedC12.valid8
#print axioms N11Formalization.C450Source23GroupedC12.valid9
#print axioms N11Formalization.C450Source23GroupedC12.valid10
#print axioms N11Formalization.C450Source23GroupedC12.valid11
#print axioms N11Formalization.C450Source23GroupedC12.valid12
#print axioms N11Formalization.C450Source23GroupedC12.bound
#print axioms N11Formalization.C450Source23GroupedC12.endpoint_checks
