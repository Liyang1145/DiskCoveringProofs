import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((6144703141:ℚ)/10000000000),((265894207:ℚ)/400000000),((3754901047:ℚ)/35600000000),((381094207:ℚ)/1984000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1258349003:ℚ)/2000000000),((283494481602308610025483578274325281:ℚ)/15464825552896000000000000000000000000),((-846287490068961711406475963:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((6620436967:ℚ)/10000000000),((3442559061:ℚ)/5000000000),((1677205281:ℚ)/15800000000),((1627519687:ℚ)/8900000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((513337971:ℚ)/1000000000),((1442270676720417855305044028469722145125702993450921309369:ℚ)/82494591168750000000000000000000000000000000000000000000000),((-893297482492432629102057347:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((3429132991:ℚ)/5000000000),((1750998231:ℚ)/2500000000),((5989132991:ℚ)/56250000000),((2470998231:ℚ)/13825000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4454812139:ℚ)/10000000000),((467967104931227202424728042869217300102152007069092251:ℚ)/27300108691406250000000000000000000000000000000000000000),((-229204975004992422764240563:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((1:ℚ)/16),((1:ℚ)/8),((6977172137:ℚ)/10000000000),((1412685751:ℚ)/2000000000),((12097172137:ℚ)/113450000000),((1988685751:ℚ)/11250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1019163189:ℚ)/2500000000),((778326681802478084323595379565048737732095323741368796611139:ℚ)/45814882434082031250000000000000000000000000000000000000000000),((-928585573183014279972469987:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((28146493:ℚ)/40000000),((3561431787:ℚ)/5000000000),((48626493:ℚ)/457600000),((5001431787:ℚ)/28362500000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3874607243:ℚ)/10000000000),((1976099732012279284206156395234337172657487535896122600543:ℚ)/116639489525361816406250000000000000000000000000000000000000),((-14951512606141514788427:ℚ)/236584960000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/16),((1:ℚ)/8),((887009137:ℚ)/1250000000),((3591148703:ℚ)/5000000000),((1527009137:ℚ)/14418750000),((5031148703:ℚ)/28600000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3662025727:ℚ)/10000000000),((1095759515989225462109995286501478082190999972611687550238881:ℚ)/64847324089762500000000000000000000000000000000000000000000000),((-14693035293910266544843987:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((7155521707:ℚ)/10000000000),((1810432569:ℚ)/2500000000),((12275521707:ℚ)/116300000000),((843477523:ℚ)/4806250000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((42961869:ℚ)/125000000),((632779734886020069336474596934373993287319804865093980783:ℚ)/37542095451569885253906250000000000000000000000000000000000),((-946239739074158153581428827:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/16),((1:ℚ)/8),((7214969113:ℚ)/10000000000),((3650581103:ℚ)/5000000000),((12334969113:ℚ)/117250000000),((5090581103:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((319673603:ℚ)/1000000000),((426128792392655273581501098515788361451638659076372104599289:ℚ)/25342306337978540039062500000000000000000000000000000000000000),((-952125981591307212356249987:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((454650959:ℚ)/625000000),((7360593221:ℚ)/10000000000),((774650959:ℚ)/7387500000),((10240593221:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((367208679:ℚ)/1250000000),((263541923918562187424323018723459867685501213336682970302527:ℚ)/15708890590658569335937500000000000000000000000000000000000000),((-3742238239372047125473363:ℚ)/57760000000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((1833465107:ℚ)/2500000000),((7479452587:ℚ)/10000000000),((3113465107:ℚ)/30025000000),((10359452587:ℚ)/59100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((530845937:ℚ)/2000000000),((93725118762540718099385106422234474817324317026293874324117829:ℚ)/5582769915665081250000000000000000000000000000000000000000000000),((-60243797803698933914683627:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((7452747263:ℚ)/10000000000),((3799154271:ℚ)/5000000000),((12572747263:ℚ)/122000000000),((5239154271:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1971712601:ℚ)/10000000000),((172541757165120583307694680656600083133501547827715707831:ℚ)/10319505826269531250000000000000000000000000000000000000000),((-975678630191901723440571187:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((757162983:ℚ)/1000000000),((8073701257:ℚ)/10000000000),((1269162983:ℚ)/12960000000),((10953701257:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((216079901:ℚ)/2500000000),((39376969045612733286506919269743816322911374142491750301213:ℚ)/2326909907812500000000000000000000000000000000000000000000000),((-9874595982027074354178947:ℚ)/147865600000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((4023560583:ℚ)/5000000000),((9974898701:ℚ)/10000000000),((6583560583:ℚ)/80000000000),((12854898701:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((5596953463675367229862869048603720442310954535344417107:ℚ)/318864600000000000000000000000000000000000000000000000000),((-68578361:ℚ)/1024000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((2487154803:ℚ)/2500000000),((2755260771:ℚ)/2000000000),((3767154803:ℚ)/55200000000),((3331260771:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((97960953362261935086398728106299643117:ℚ)/4875264000000000000000000000000000000000),((-68578361:ℚ)/1024000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC18
#check @N11Formalization.C450TenthGroupedC18.bound
#print axioms N11Formalization.C450TenthGroupedC18.valid0
#print axioms N11Formalization.C450TenthGroupedC18.valid1
#print axioms N11Formalization.C450TenthGroupedC18.valid2
#print axioms N11Formalization.C450TenthGroupedC18.valid3
#print axioms N11Formalization.C450TenthGroupedC18.valid4
#print axioms N11Formalization.C450TenthGroupedC18.valid5
#print axioms N11Formalization.C450TenthGroupedC18.valid6
#print axioms N11Formalization.C450TenthGroupedC18.valid7
#print axioms N11Formalization.C450TenthGroupedC18.valid8
#print axioms N11Formalization.C450TenthGroupedC18.valid9
#print axioms N11Formalization.C450TenthGroupedC18.valid10
#print axioms N11Formalization.C450TenthGroupedC18.valid11
#print axioms N11Formalization.C450TenthGroupedC18.valid12
#print axioms N11Formalization.C450TenthGroupedC18.valid13
#print axioms N11Formalization.C450TenthGroupedC18.bound
#print axioms N11Formalization.C450TenthGroupedC18.endpoint_checks
