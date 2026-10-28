import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((1533910907:ℚ)/2500000000),((6634608459:ℚ)/10000000000),((5401732721:ℚ)/26700000000),((7594608459:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6311973279:ℚ)/10000000000),((1040667460879435036519175744857797785887:ℚ)/135921318336000000000000000000000000000000),((-15884538077409385421291:ℚ)/320000000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((6610953827:ℚ)/10000000000),((6872207847:ℚ)/10000000000),((3290408783:ℚ)/15800000000),((2610735949:ℚ)/8900000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2579365631:ℚ)/5000000000),((291758260204003381012799462957405477818835702172594972977:ℚ)/41247295584375000000000000000000000000000000000000000000000),((-94296988604367703770566771:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((3424296463:ℚ)/5000000000),((3495502511:ℚ)/5000000000),((11872889389:ℚ)/56250000000),((3975502511:ℚ)/13825000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((280266213:ℚ)/625000000),((652583271030368529889477021199649373106272020709491487:ℚ)/95550380419921875000000000000000000000000000000000000000),((-23894673839831300455774331:ℚ)/462080000000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((3:ℚ)/16),((1:ℚ)/4),((1741852237:ℚ)/2500000000),((7050403017:ℚ)/10000000000),((6025556711:ℚ)/28362500000),((2670134339:ℚ)/9375000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((4108934103:ℚ)/10000000000),((89060989867974297798356420504233553855859585008106773210741:ℚ)/13256621074676513671875000000000000000000000000000000000000000),((-6013843162081677421120531:ℚ)/115520000000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((702681613:ℚ)/1000000000),((7109800629:ℚ)/10000000000),((220731349:ℚ)/1040000000),((8069800629:ℚ)/28362500000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3908618011:ℚ)/10000000000),((3224995885195614128104262587359481327083605923550732479:ℚ)/481981361675048828125000000000000000000000000000000000000),((-965433739271001077622931:ℚ)/18483200000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/16),((1:ℚ)/4),((885777847:ℚ)/1250000000),((7169197869:ℚ)/10000000000),((3057333541:ℚ)/14418750000),((625322913:ℚ)/2200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((115564157:ℚ)/312500000),((98366112241264300374390183667245123371235355530768766141:ℚ)/14758152956250000000000000000000000000000000000000000000000),((-1513524705474623899481291:ℚ)/28880000000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((7145628901:ℚ)/10000000000),((1445718949:ℚ)/2000000000),((24636886703:ℚ)/116300000000),((1637718949:ℚ)/5767500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((27151349:ℚ)/78125000),((71797302869699816732685875221967893474545958870656168617:ℚ)/10812123490052126953125000000000000000000000000000000000000),((-97188112335768926252718499:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/16),((1:ℚ)/4),((7205034517:ℚ)/10000000000),((7287991267:ℚ)/10000000000),((3545014793:ℚ)/16750000000),((8247991267:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3238074083:ℚ)/10000000000),((1711073321838935572845131481085874953533246087944767455959:ℚ)/258594962632434082031250000000000000000000000000000000000000),((-270113483490114465199051:ℚ)/5120000000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((1816109909:ℚ)/2500000000),((3673693721:ℚ)/5000000000),((6248329727:ℚ)/29550000000),((4153693721:ℚ)/14656250000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((745666397:ℚ)/2500000000),((5665002770854445696778839458151315278356936729883207226639:ℚ)/859079954176640510559082031250000000000000000000000000000000),((-6114634176236215889422019:ℚ)/115520000000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/16),((1:ℚ)/4),((7323844271:ℚ)/10000000000),((92584791:ℚ)/125000000),((25171532813:ℚ)/119150000000),((34861597:ℚ)/123125000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((2704015233:ℚ)/10000000000),((653142510140368158019916933913564688038861527803048421:ℚ)/99370641073601531982421875000000000000000000000000000000),((-98157650237942279583196859:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((7383248433:ℚ)/10000000000),((1866544697:ℚ)/2500000000),((25349745299:ℚ)/120100000000),((2106544697:ℚ)/7446875000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2394015379:ℚ)/10000000000),((3049267683131189406124242528783414986555851751840394010067:ℚ)/465369843667142081260681152343750000000000000000000000000000),((-98481477846426836442185211:ℚ)/1848320000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((7442652133:ℚ)/10000000000),((1516993769:ℚ)/2000000000),((25527956399:ℚ)/122000000000),((1708993769:ℚ)/6005000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2038406443:ℚ)/10000000000),((16570998187848624337057356274810004287545461782616115479:ℚ)/2517959421609765625000000000000000000000000000000000000000),((-98805629697482257471151011:ℚ)/1848320000000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((7561458191:ℚ)/10000000000),((4030058661:ℚ)/5000000000),((25884374573:ℚ)/129600000000),((4510058661:ℚ)/15250000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((251882483:ℚ)/2500000000),((123859448163768115088538712627968562592539289447058785371:ℚ)/18178983654785156250000000000000000000000000000000000000000),((-99454906337512665310877819:ℚ)/1848320000000000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((4018332989:ℚ)/5000000000),((9960570129:ℚ)/10000000000),((13654998967:ℚ)/80000000000),((1213396681:ℚ)/3600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((205247723529750572435115324890000602222819960587437:ℚ)/27337500000000000000000000000000000000000000000000000),((-1380413:ℚ)/25600000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((9937299633:ℚ)/10000000000),((13761101607:ℚ)/10000000000),((33011898899:ℚ)/220800000000),((14721101607:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((347797042062522510032892064858402620371:ℚ)/38088000000000000000000000000000000000000),((-1380413:ℚ)/25600000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC20
#check @N11Formalization.C450SeventhGroupedC20.bound
#print axioms N11Formalization.C450SeventhGroupedC20.valid0
#print axioms N11Formalization.C450SeventhGroupedC20.valid1
#print axioms N11Formalization.C450SeventhGroupedC20.valid2
#print axioms N11Formalization.C450SeventhGroupedC20.valid3
#print axioms N11Formalization.C450SeventhGroupedC20.valid4
#print axioms N11Formalization.C450SeventhGroupedC20.valid5
#print axioms N11Formalization.C450SeventhGroupedC20.valid6
#print axioms N11Formalization.C450SeventhGroupedC20.valid7
#print axioms N11Formalization.C450SeventhGroupedC20.valid8
#print axioms N11Formalization.C450SeventhGroupedC20.valid9
#print axioms N11Formalization.C450SeventhGroupedC20.valid10
#print axioms N11Formalization.C450SeventhGroupedC20.valid11
#print axioms N11Formalization.C450SeventhGroupedC20.valid12
#print axioms N11Formalization.C450SeventhGroupedC20.valid13
#print axioms N11Formalization.C450SeventhGroupedC20.valid14
#print axioms N11Formalization.C450SeventhGroupedC20.bound
#print axioms N11Formalization.C450SeventhGroupedC20.endpoint_checks
