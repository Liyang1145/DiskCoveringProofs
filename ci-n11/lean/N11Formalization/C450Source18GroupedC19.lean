import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((754551957:ℚ)/1250000000),((6564729117:ℚ)/10000000000),((1394551957:ℚ)/6675000000),((30574187351:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1305998163:ℚ)/2000000000),((471992604417267430144297293531114122104969:ℚ)/8698964373504000000000000000000000000000000),((-149248445031537770133381589:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((6513996911:ℚ)/10000000000),((340163683:ℚ)/500000000),((11633996911:ℚ)/55300000000),((1564491049:ℚ)/5340000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((338233311:ℚ)/625000000),((22139418669598044257268062409987079365473676497393648653279:ℚ)/436561376465025000000000000000000000000000000000000000000000),((-393025665026353115386389:ℚ)/1848320000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((84408169:ℚ)/125000000),((865314913:ℚ)/1250000000),((148408169:ℚ)/703125000),((3955944739:ℚ)/13825000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4767150801:ℚ)/10000000000),((59595144701374068844627101318699367694227941311526031:ℚ)/1209498486328125000000000000000000000000000000000000000),((-2518521261032942581727469:ℚ)/11552000000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((21474851:ℚ)/31250000),((7041748383:ℚ)/10000000000),((37474851:ℚ)/178750000),((32005245149:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((275802147:ℚ)/625000000),((4453588753756512878559283654159404060996953265764957567309977:ℚ)/90987066650390625000000000000000000000000000000000000000000000),((-163102219523164782475396589:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((6991232767:ℚ)/10000000000),((3580480859:ℚ)/5000000000),((12111232767:ℚ)/58150000000),((16181442577:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((161189339:ℚ)/400000000),((28865705325720842840939322975016359957926418184015087923647983:ℚ)/593278760667450000000000000000000000000000000000000000000000000),((-2171268736774616358896999:ℚ)/9728000000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((7110495771:ℚ)/10000000000),((910020009:ℚ)/1250000000),((12230495771:ℚ)/59100000000),((4090060027:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3608655881:ℚ)/10000000000),((13523399177472261846444196202142517007522238791190840437597:ℚ)/279455666763258361816406250000000000000000000000000000000000),((-2608249840753979225895181:ℚ)/11552000000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((3614871089:ℚ)/5000000000),((3699672081:ℚ)/5000000000),((6174871089:ℚ)/30025000000),((16539016243:ℚ)/59100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((3134291999:ℚ)/10000000000),((134427459137201587092421413380543620948953993365550365933904373:ℚ)/2791384957832540625000000000000000000000000000000000000000000000),((-42209232885991777081363661:ℚ)/184832000000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((7348972783:ℚ)/10000000000),((375925733:ℚ)/500000000),((12468972783:ℚ)/61000000000),((1671777199:ℚ)/6005000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((644334393:ℚ)/2500000000),((120738995174994175061933192271619411437830137999180275587:ℚ)/2517959421609765625000000000000000000000000000000000000000),((-426858157258796425529189:ℚ)/1848320000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((746818833:ℚ)/1000000000),((7756817357:ℚ)/10000000000),((1258818833:ℚ)/6290000000),((34150452071:ℚ)/122000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1865154559:ℚ)/10000000000),((27125835496372614208902868270929423167030127866930279531277363:ℚ)/561268686381250000000000000000000000000000000000000000000000000),((-11361485774200829:ℚ)/48640000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((7706577001:ℚ)/10000000000),((3997536379:ℚ)/5000000000),((4275525667:ℚ)/21600000000),((17432609137:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((27220840314691342897219931500911826323852057773623626804029:ℚ)/566930061815625000000000000000000000000000000000000000000000),((-60583447:ℚ)/256000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((7944913283:ℚ)/10000000000),((247495491:ℚ)/250000000),((13064913283:ℚ)/80000000000),((1014486473:ℚ)/3240000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1070980389262860731587085837335538899877719945312487:ℚ)/19929037500000000000000000000000000000000000000000000),((-60583447:ℚ)/256000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((4925083937:ℚ)/5000000000),((6852691783:ℚ)/5000000000),((2495027979:ℚ)/18400000000),((25998075349:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2203750883051202758887153619804926314891:ℚ)/33856000000000000000000000000000000000000),((-60583447:ℚ)/256000000)⟩
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
end N11Formalization.C450Source18GroupedC19
#check @N11Formalization.C450Source18GroupedC19.bound
#print axioms N11Formalization.C450Source18GroupedC19.valid0
#print axioms N11Formalization.C450Source18GroupedC19.valid1
#print axioms N11Formalization.C450Source18GroupedC19.valid2
#print axioms N11Formalization.C450Source18GroupedC19.valid3
#print axioms N11Formalization.C450Source18GroupedC19.valid4
#print axioms N11Formalization.C450Source18GroupedC19.valid5
#print axioms N11Formalization.C450Source18GroupedC19.valid6
#print axioms N11Formalization.C450Source18GroupedC19.valid7
#print axioms N11Formalization.C450Source18GroupedC19.valid8
#print axioms N11Formalization.C450Source18GroupedC19.valid9
#print axioms N11Formalization.C450Source18GroupedC19.valid10
#print axioms N11Formalization.C450Source18GroupedC19.valid11
#print axioms N11Formalization.C450Source18GroupedC19.bound
#print axioms N11Formalization.C450Source18GroupedC19.endpoint_checks
