import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((6312899157:ℚ)/10000000000),((658685553:ℚ)/1000000000),((-4098798871:ℚ)/9920000000),((-16058697471:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1476329783:ℚ)/2500000000),((661012913337734469388869584542089955401078436792911820611:ℚ)/26464482031250000000000000000000000000000000000000000000000),((13496767961221690063300277:ℚ)/147865600000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((3275330707:ℚ)/5000000000),((3412322831:ℚ)/5000000000),((-21326259817:ℚ)/51500000000),((-2795330707:ℚ)/8900000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((2658670451:ℚ)/5000000000),((2821676039441530464909729638845209530873824570217454679:ℚ)/113455948437500000000000000000000000000000000000000000000),((334258543876641360025361333:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((6788404979:ℚ)/10000000000),((1735883277:ℚ)/2500000000),((-10871182939:ℚ)/26700000000),((-17485214937:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4663593391:ℚ)/10000000000),((73034624429886597252769007662808675028466369257833498009:ℚ)/3010231647656250000000000000000000000000000000000000000000),((82711129619920753572987037:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((6907270367:ℚ)/10000000000),((3501487521:ℚ)/5000000000),((-21950412647:ℚ)/54350000000),((-5947270367:ℚ)/18275000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((1075685773:ℚ)/2500000000),((248548999966394499744057788484760945108936012977471689611:ℚ)/10366251160083007812500000000000000000000000000000000000000),((329139332996543231840685973:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((6966701559:ℚ)/10000000000),((441400989:ℚ)/625000000),((-162929819:ℚ)/403125000),((-18020104677:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4111263747:ℚ)/10000000000),((7293761674975114758212855907518331414538557318525538769:ℚ)/304345656152343750000000000000000000000000000000000000000),((270029318292085978089527:ℚ)/3040000000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((878266473:ℚ)/1250000000),((7121855483:ℚ)/10000000000),((-44732988381:ℚ)/110600000000),((-2274799419:ℚ)/6971875000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((488872603:ℚ)/1250000000),((250507532299153106112188655964307117215689927262653199:ℚ)/10457693325150012969970703125000000000000000000000000000),((1310292544782568751395344717:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-7:ℚ)/16),((-3:ℚ)/8),((7085561067:ℚ)/10000000000),((7151574901:ℚ)/10000000000),((-44941024307:ℚ)/111550000000),((-18376683201:ℚ)/56012500000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((462557651:ℚ)/1250000000),((2334727305319656914076863097365367007857754957158372930429:ℚ)/98015430042026855468750000000000000000000000000000000000000),((68783616938315349312810687:ℚ)/778240000000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((7115275363:ℚ)/10000000000),((7181294049:ℚ)/10000000000),((-45149058343:ℚ)/112025000000),((-6155275363:ℚ)/18750000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((897700551:ℚ)/2500000000),((51523006797367511770907334965614691266861933876141706051:ℚ)/2163416147232055664062500000000000000000000000000000000000),((1305326623048386421041656853:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-7:ℚ)/16),((-3:ℚ)/8),((7144989433:ℚ)/10000000000),((7211012931:ℚ)/10000000000),((-45357090517:ℚ)/112500000000),((-18554968299:ℚ)/56487500000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((3477842313:ℚ)/10000000000),((241413445951042248856605975013710209551808778966136549529:ℚ)/10138637368542480468750000000000000000000000000000000000000),((1303765690408782038561559933:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((3587351639:ℚ)/5000000000),((7240731549:ℚ)/10000000000),((-45565120843:ℚ)/112975000000),((-9322054917:ℚ)/28362500000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((3361248237:ℚ)/10000000000),((38353039633710728789748592791926678066243823315583759073:ℚ)/1611001311693450927734375000000000000000000000000000000000),((1302205923835165691841281853:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-7:ℚ)/16),((-3:ℚ)/8),((7204416903:ℚ)/10000000000),((7270449907:ℚ)/10000000000),((-45773149349:ℚ)/113450000000),((-6244416903:ℚ)/18987500000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((1620313591:ℚ)/5000000000),((330101152945803363461149659151191796960658555555897952911:ℚ)/13868191621740722656250000000000000000000000000000000000000),((1300647323025081608537344797:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((723413031:ℚ)/1000000000),((7300168009:ℚ)/10000000000),((-45981176063:ℚ)/113925000000),((-1882239093:ℚ)/5720000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((623102179:ℚ)/2000000000),((18121781072834221572060214621248015684854704621747568957:ℚ)/761463502800000000000000000000000000000000000000000000000),((1299089887862518499171617893:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((7263843501:ℚ)/10000000000),((1471920691:ℚ)/2000000000),((-713803449:ℚ)/1760000000),((-6303843501:ℚ)/19225000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((597066731:ℚ)/2000000000),((41484449617843213477313644629618418847940619948839:ℚ)/1734758792877197265625000000000000000000000000000000),((51912758459999805287208093:ℚ)/591462400000000000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((57213041:ℚ)/78125000),((927379739:ℚ)/1250000000),((-5851658173:ℚ)/14418750000),((-149139123:ℚ)/454296875),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2706846273:ℚ)/10000000000),((129265499549375246968839817132778310809442135167022979:ℚ)/5407628539694845676422119140625000000000000000000000000),((20229878472445229536416013:ℚ)/231040000000000000000000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((1845673541:ℚ)/2500000000),((1507580791:ℚ)/2000000000),((-9529065537:ℚ)/23260000000),((-1605673541:ℚ)/4925000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((239708909:ℚ)/1000000000),((5237147146159621243655785176002634694598952464534107413:ℚ)/217079316381835937500000000000000000000000000000000000000),((51687740125750178762942693:ℚ)/591462400000000000000000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/16),((-3:ℚ)/8),((1875385397:ℚ)/2500000000),((3887812591:ℚ)/5000000000),((-8218229379:ℚ)/19700000000),((-4906156191:ℚ)/15250000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((64456183:ℚ)/400000000),((107179594855838143323253661513904058692620177251496383017:ℚ)/4366724316406250000000000000000000000000000000000000000000),((21142210972757371:ℚ)/243200000000000000)⟩
theorem valid15 : Valid tenth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((7739227321:ℚ)/10000000000),((8251028667:ℚ)/10000000000),((-862904929:ℚ)/2000000000),((-6779227321:ℚ)/21600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((531198854398067850463828413185932018753602302898660097:ℚ)/20995200000000000000000000000000000000000000000000000000),((17719499:ℚ)/204800000)⟩
theorem valid16 : Valid tenth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((2053641519:ℚ)/2500000000),((5076129471:ℚ)/5000000000),((-32972906297:ℚ)/64800000000),((-5440924557:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((118158501830745603293993957228922526162375956597767017663:ℚ)/4050000000000000000000000000000000000000000000000000000000),((17719499:ℚ)/204800000)⟩
theorem valid17 : Valid tenth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((10115599029:ℚ)/10000000000),((2790740521:ℚ)/2000000000),((-18511183647:ℚ)/32000000000),((-398069523:ℚ)/1600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((213304810344505196911307898182793375224189279017097:ℚ)/6400000000000000000000000000000000000000000000000000),((17719499:ℚ)/204800000)⟩
theorem valid18 : Valid tenth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound tenth nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound tenth nn0 nn1 Qcell ((4481:ℚ)/6400) ((4519:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound tenth nn0 nn1 Qcell ((2193:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((4519:ℚ)/6400) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((4557:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound tenth nn0 nn1 Qcell ((4557:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC10
#check @N11Formalization.C450TenthGroupedC10.bound
#print axioms N11Formalization.C450TenthGroupedC10.valid0
#print axioms N11Formalization.C450TenthGroupedC10.valid1
#print axioms N11Formalization.C450TenthGroupedC10.valid2
#print axioms N11Formalization.C450TenthGroupedC10.valid3
#print axioms N11Formalization.C450TenthGroupedC10.valid4
#print axioms N11Formalization.C450TenthGroupedC10.valid5
#print axioms N11Formalization.C450TenthGroupedC10.valid6
#print axioms N11Formalization.C450TenthGroupedC10.valid7
#print axioms N11Formalization.C450TenthGroupedC10.valid8
#print axioms N11Formalization.C450TenthGroupedC10.valid9
#print axioms N11Formalization.C450TenthGroupedC10.valid10
#print axioms N11Formalization.C450TenthGroupedC10.valid11
#print axioms N11Formalization.C450TenthGroupedC10.valid12
#print axioms N11Formalization.C450TenthGroupedC10.valid13
#print axioms N11Formalization.C450TenthGroupedC10.valid14
#print axioms N11Formalization.C450TenthGroupedC10.valid15
#print axioms N11Formalization.C450TenthGroupedC10.valid16
#print axioms N11Formalization.C450TenthGroupedC10.valid17
#print axioms N11Formalization.C450TenthGroupedC10.valid18
#print axioms N11Formalization.C450TenthGroupedC10.bound
#print axioms N11Formalization.C450TenthGroupedC10.endpoint_checks
