import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((3105185627:ℚ)/5000000000),((3352108299:ℚ)/5000000000),((-2392108299:ℚ)/24800000000),((-288395209:ℚ)/17800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3071699561:ℚ)/5000000000),((3849695214216729412933298026627268046293603400546610153:ℚ)/273175487500000000000000000000000000000000000000000000000),((2702242951020509515533443:ℚ)/1386240000000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((334285043:ℚ)/500000000),((6823067773:ℚ)/10000000000),((-4903067773:ℚ)/53400000000),((-110285043:ℚ)/5435000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((198228267:ℚ)/400000000),((1218068632863383944799869689068750861081370062469131381:ℚ)/89303538880468750000000000000000000000000000000000000000),((198269275646697850312849:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((6804526053:ℚ)/10000000000),((1735478867:ℚ)/2500000000),((-1255478867:ℚ)/13587500000),((-2324526053:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2308097203:ℚ)/5000000000),((5852059463771134516033808776942762903128833616706970418871:ℚ)/430840204216406250000000000000000000000000000000000000000000),((-2015984353662471341589:ℚ)/6080000000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((6923348661:ℚ)/10000000000),((3500669033:ℚ)/5000000000),((-362952719:ℚ)/3950000000),((-2443348661:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1062935281:ℚ)/2500000000),((578434607005612885694421669748581898425464637998814636677:ℚ)/42834711859814453125000000000000000000000000000000000000000),((-362535010630823501226791:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((1745689759:ℚ)/2500000000),((7060759859:ℚ)/10000000000),((-5140759859:ℚ)/55775000000),((-208563253:ℚ)/9375000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4058071043:ℚ)/10000000000),((1814891083718332410476631587370411667317124585559708527:ℚ)/134640187025070190429687500000000000000000000000000000000),((-1855116785042134115490639:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((7042168813:ℚ)/10000000000),((1780045217:ℚ)/2500000000),((-1300045217:ℚ)/14062500000),((-2562168813:ℚ)/113450000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1927624693:ℚ)/5000000000),((921042595780702891037894993029900362158086825133725793:ℚ)/68447057279296875000000000000000000000000000000000000000),((-141241289609152510044791:ℚ)/115520000000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((7101578007:ℚ)/10000000000),((7179601111:ℚ)/10000000000),((-5259601111:ℚ)/56725000000),((-2621578007:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3641743477:ℚ)/10000000000),((285231501560152117503788371692708713136313829161958062198149:ℚ)/21232082185600000000000000000000000000000000000000000000000000),((-2664371698406071356440999:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((7160986633:ℚ)/10000000000),((113109697:ℚ)/156250000),((-7555427:ℚ)/81250000),((-893662211:ℚ)/38450000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((213471633:ℚ)/625000000),((7259533901411351442104245858824602696661826732545547:ℚ)/541244743377685546875000000000000000000000000000000000),((-5852985549115801157:ℚ)/3525390625000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((1444078941:ℚ)/2000000000),((3649219689:ℚ)/5000000000),((-896406563:ℚ)/9612500000),((-548078941:ℚ)/23260000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3173940627:ℚ)/10000000000),((810009587846959273726871029061145864762836446411156755787:ℚ)/60483301372150000000000000000000000000000000000000000000000),((-2604521927024151880679797:ℚ)/1386240000000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-1:ℚ)/8),((-1:ℚ)/16),((1819950559:ℚ)/2500000000),((3678928719:ℚ)/5000000000),((-2718928719:ℚ)/29075000000),((-99992937:ℚ)/4187500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((116523639:ℚ)/400000000),((7137519223506597383537885342068727063653949963132819757:ℚ)/533733168029785156250000000000000000000000000000000000000),((-2907381928959758082409477:ℚ)/1386240000000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((7339209239:ℚ)/10000000000),((1854318701:ℚ)/2500000000),((-196331243:ℚ)/2093750000),((-2859209239:ℚ)/118200000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((525453237:ℚ)/2000000000),((769565647708628176942220896114825496296915822575354265937:ℚ)/57626998987500000000000000000000000000000000000000000000000),((-267505636898179636181519:ℚ)/115520000000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((462413483:ℚ)/625000000),((301444301:ℚ)/400000000),((-224644301:ℚ)/2364000000),((-182413483:ℚ)/7506250000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2307196913:ℚ)/10000000000),((5218347272809704359756695430858701702672749547760735539:ℚ)/390549945141220092773437500000000000000000000000000000000),((-7447240389667188074319:ℚ)/2957312000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((7517427209:ℚ)/10000000000),((3827468833:ℚ)/5000000000),((-2867468833:ℚ)/30025000000),((-3037427209:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1475437039:ℚ)/10000000000),((545000327202556196885255994411862498156281239984587316349149:ℚ)/40890627150000000000000000000000000000000000000000000000000000),((-180501133927443:ℚ)/60800000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((3818118387:ℚ)/5000000000),((1016279339:ℚ)/1250000000),((-776279339:ℚ)/7625000000),((-1578118387:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((464784890514770438904942015867695603759125089124998392627:ℚ)/34579094400000000000000000000000000000000000000000000000000),((-421589:ℚ)/128000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((2027864389:ℚ)/2500000000),((2507785127:ℚ)/2500000000),((-2027785127:ℚ)/16200000000),((-907864389:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((149671292759056742309871496726388947403313018399395259521:ℚ)/10800000000000000000000000000000000000000000000000000000000),((-421589:ℚ)/128000000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((2503032709:ℚ)/2500000000),((3458050881:ℚ)/2500000000),((-2978050881:ℚ)/20000000000),((-461010903:ℚ)/18400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((147558200082513230370837629845172520439633924822780129:ℚ)/9733600000000000000000000000000000000000000000000000000),((-421589:ℚ)/128000000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC15
#check @N11Formalization.C450EighthGroupedC15.bound
#print axioms N11Formalization.C450EighthGroupedC15.valid0
#print axioms N11Formalization.C450EighthGroupedC15.valid1
#print axioms N11Formalization.C450EighthGroupedC15.valid2
#print axioms N11Formalization.C450EighthGroupedC15.valid3
#print axioms N11Formalization.C450EighthGroupedC15.valid4
#print axioms N11Formalization.C450EighthGroupedC15.valid5
#print axioms N11Formalization.C450EighthGroupedC15.valid6
#print axioms N11Formalization.C450EighthGroupedC15.valid7
#print axioms N11Formalization.C450EighthGroupedC15.valid8
#print axioms N11Formalization.C450EighthGroupedC15.valid9
#print axioms N11Formalization.C450EighthGroupedC15.valid10
#print axioms N11Formalization.C450EighthGroupedC15.valid11
#print axioms N11Formalization.C450EighthGroupedC15.valid12
#print axioms N11Formalization.C450EighthGroupedC15.valid13
#print axioms N11Formalization.C450EighthGroupedC15.valid14
#print axioms N11Formalization.C450EighthGroupedC15.valid15
#print axioms N11Formalization.C450EighthGroupedC15.bound
#print axioms N11Formalization.C450EighthGroupedC15.endpoint_checks
