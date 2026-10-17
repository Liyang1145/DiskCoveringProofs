import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((11907519:ℚ)/20000000),((3243086857:ℚ)/5000000000),((17027519:ℚ)/53400000),((4331086857:ℚ)/9920000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6706957781:ℚ)/10000000000),((354043505575403867684468948386026676567:ℚ)/8698964373504000000000000000000000000000),((-9028839641502364526731567:ℚ)/36966400000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((6431172269:ℚ)/10000000000),((1681167051:ℚ)/2500000000),((8991172269:ℚ)/27650000000),((2225167051:ℚ)/5340000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((35123143:ℚ)/62500000),((15924246226175288194151962444075980218993663310882912112021:ℚ)/436561376465025000000000000000000000000000000000000000000000),((-2341214470078761512032583:ℚ)/9241600000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((1667438361:ℚ)/2500000000),((1368778021:ℚ)/2000000000),((2307438361:ℚ)/7031250000),((1803978021:ℚ)/4424000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((999930851:ℚ)/2000000000),((1374897985099666919026654137399764310755966317309289:ℚ)/39632846400000000000000000000000000000000000000000000),((-1525201106141465652427303:ℚ)/5914624000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((6789016463:ℚ)/10000000000),((6963096239:ℚ)/10000000000),((9349016463:ℚ)/28600000000),((3046365413:ℚ)/7500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2330901833:ℚ)/5000000000),((927394761454475701911980420790109110574208186437342868881:ℚ)/26959130859375000000000000000000000000000000000000000000000),((-38444135808907341903883743:ℚ)/147865600000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((3454131167:ℚ)/5000000000),((7082287387:ℚ)/10000000000),((4734131167:ℚ)/14537500000),((9258287387:ℚ)/22880000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4299612903:ℚ)/10000000000),((1296294180463167387083651818599859183758229356341307786909053:ℚ)/37969840682716800000000000000000000000000000000000000000000000),((-38757481513789022156329127:ℚ)/147865600000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((109804561:ℚ)/156250000),((1800366069:ℚ)/2500000000),((149804561:ℚ)/461718750),((2344366069:ℚ)/5815000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((488285433:ℚ)/1250000000),((202158587505648932657551118684758443192190031538702242977:ℚ)/5961720890949511718750000000000000000000000000000000000000),((-2441879206245756023705863:ℚ)/9241600000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((7146705967:ℚ)/10000000000),((7320627587:ℚ)/10000000000),((9706705967:ℚ)/30025000000),((3165542529:ℚ)/7880000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((3471209207:ℚ)/10000000000),((74340956229777965451340219406681415321325934091550575245557:ℚ)/2205538732114600000000000000000000000000000000000000000000000),((-39381895540527372382737527:ℚ)/147865600000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((7265905263:ℚ)/10000000000),((185994449:ℚ)/250000000),((9825905263:ℚ)/30500000000),((240394449:ℚ)/600500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((372012019:ℚ)/1250000000),((84426711999937864296188822376069872578670733028535837:ℚ)/2517959421609765625000000000000000000000000000000000000),((-24808105279209645993583:ℚ)/92416000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((7385090487:ℚ)/10000000000),((959755281:ℚ)/1250000000),((9945090487:ℚ)/31450000000),((1231755281:ℚ)/3050000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((2383772299:ℚ)/10000000000),((300827810224321747404387554202535616053532488848458437653:ℚ)/8769823224707031250000000000000000000000000000000000000000),((-6923058037682713:ℚ)/25600000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((762342129:ℚ)/1000000000),((3958130757:ℚ)/5000000000),((1018342129:ℚ)/3240000000),((296831221:ℚ)/740000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((282764054294932906058964782732107740256343422951986257:ℚ)/8308358325000000000000000000000000000000000000000000000),((-70340009:ℚ)/256000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((1965425783:ℚ)/2500000000),((1964156307:ℚ)/2000000000),((2605425783:ℚ)/10000000000),((2399356307:ℚ)/5184000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3525667443331322123219862819229674316758120698812373:ℚ)/81629337600000000000000000000000000000000000000000000),((-70340009:ℚ)/256000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((9766616003:ℚ)/10000000000),((6813039969:ℚ)/5000000000),((4108872001:ℚ)/18400000000),((7901039969:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((15359352216200581343063622443635227831:ℚ)/270848000000000000000000000000000000000),((-70340009:ℚ)/256000000)⟩
theorem valid11 : Valid source18 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source18 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC21
#check @N11Formalization.C450Source18GroupedC21.bound
#print axioms N11Formalization.C450Source18GroupedC21.valid0
#print axioms N11Formalization.C450Source18GroupedC21.valid1
#print axioms N11Formalization.C450Source18GroupedC21.valid2
#print axioms N11Formalization.C450Source18GroupedC21.valid3
#print axioms N11Formalization.C450Source18GroupedC21.valid4
#print axioms N11Formalization.C450Source18GroupedC21.valid5
#print axioms N11Formalization.C450Source18GroupedC21.valid6
#print axioms N11Formalization.C450Source18GroupedC21.valid7
#print axioms N11Formalization.C450Source18GroupedC21.valid8
#print axioms N11Formalization.C450Source18GroupedC21.valid9
#print axioms N11Formalization.C450Source18GroupedC21.valid10
#print axioms N11Formalization.C450Source18GroupedC21.valid11
#print axioms N11Formalization.C450Source18GroupedC21.bound
#print axioms N11Formalization.C450Source18GroupedC21.endpoint_checks
