import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((5925425729:ℚ)/10000000000),((806369229:ℚ)/1250000000),((23433227673:ℚ)/35600000000),((2599107687:ℚ)/3100000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6766716041:ℚ)/10000000000),((-170329528734046439972422897044584441:ℚ)/11279504000000000000000000000000000000),((-41132896592239761181328757:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((3200375727:ℚ)/5000000000),((6688592931:ℚ)/10000000000),((37764132997:ℚ)/55300000000),((7168592931:ℚ)/8900000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5694379571:ℚ)/10000000000),((-1158081366536064290107831583338991335968485438820753469:ℚ)/64711368750000000000000000000000000000000000000000000000),((-10280187178272381915414933:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((11:ℚ)/16),((3:ℚ)/4),((3319198757:ℚ)/5000000000),((6807408953:ℚ)/10000000000),((39071186327:ℚ)/56250000000),((21862226859:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5085050001:ℚ)/10000000000),((-7116567244615325795899222826297314707175982738081355991:ℚ)/370788574218750000000000000000000000000000000000000000000),((-10278917504221571167852973:ℚ)/57760000000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((6757216841:ℚ)/10000000000),((6926222781:ℚ)/10000000000),((79449385251:ℚ)/114400000000),((2468740927:ℚ)/3125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((594256107:ℚ)/1250000000),((-16363257590966811762468597123186359647298692117361403091:ℚ)/850678400000000000000000000000000000000000000000000000000),((-41101734850240272551314437:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((6876033863:ℚ)/10000000000),((3492814453:ℚ)/5000000000),((26918790831:ℚ)/38450000000),((11198443359:ℚ)/14300000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((4400243351:ℚ)/10000000000),((-1762739557783192300562263469509910565818526810734356869:ℚ)/88819650195312500000000000000000000000000000000000000000),((-41099610265322313724173413:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((1387088309:ℚ)/2000000000),((3522517261:ℚ)/5000000000),((16281971399:ℚ)/23260000000),((3762517261:ℚ)/4806250000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((4212999569:ℚ)/10000000000),((-62475784818648156661089854987553043330669854698281421:ℚ)/3146075494000000000000000000000000000000000000000000000),((-1643711518948874693909837:ℚ)/9241600000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((11:ℚ)/16),((3:ℚ)/4),((6994848693:ℚ)/10000000000),((7104439641:ℚ)/10000000000),((82063335623:ℚ)/117250000000),((22753318923:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2008791863:ℚ)/5000000000),((-21447232007999517619092811692346005245017862844393713153:ℚ)/1079398461914062500000000000000000000000000000000000000000),((-41086007218708041901079373:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((7054255319:ℚ)/10000000000),((1790961069:ℚ)/2500000000),((27572269503:ℚ)/39400000000),((85565421:ℚ)/109375000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((476591963:ℚ)/1250000000),((-1899891836168149704550250178852128800027247703729147917:ℚ)/95567162500000000000000000000000000000000000000000000000),((-41079267997608994656179397:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((7113661437:ℚ)/10000000000),((3611624219:ℚ)/5000000000),((83370275807:ℚ)/119150000000),((3851624219:ℚ)/4925000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3596840337:ℚ)/10000000000),((-630839143420226330355360571433177776925729648377836545351:ℚ)/31716365360156250000000000000000000000000000000000000000000),((-41072570308345668138502813:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((3586533529:ℚ)/5000000000),((3641326069:ℚ)/5000000000),((42011868819:ℚ)/60050000000),((11643978207:ℚ)/14893750000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((841942373:ℚ)/2500000000),((-1683193573106215461116905711722657573545128845713240641:ℚ)/84586113330078125000000000000000000000000000000000000000),((-10266478537156294996203557:ℚ)/57760000000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((3616236097:ℚ)/5000000000),((7342055387:ℚ)/10000000000),((4704288563:ℚ)/6725000000),((23466166161:ℚ)/30025000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((780655109:ℚ)/2500000000),((-37842236953339452287015157115750344335468599237540833:ℚ)/1900889550781250000000000000000000000000000000000000000),((-10264824879067597577864693:ℚ)/57760000000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((7291876857:ℚ)/10000000000),((1850364549:ℚ)/2500000000),((85330645427:ℚ)/122000000000),((656788183:ℚ)/840625000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((571450569:ℚ)/2000000000),((-226021574504506505757820476880854267577960777439044093937:ℚ)/11349050000000000000000000000000000000000000000000000000000),((-41052726409137683570284773:ℚ)/231040000000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((3675640529:ℚ)/5000000000),((3760131267:ℚ)/5000000000),((42992045819:ℚ)/61950000000),((12000393801:ℚ)/15250000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1282697381:ℚ)/5000000000),((-16336645924659016142537182306917483909665094069764281:ℚ)/842374804687500000000000000000000000000000000000000000),((-10258637781618101928865557:ℚ)/57760000000000000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((1494017623:ℚ)/2000000000),((763906523:ℚ)/1000000000),((17458193853:ℚ)/25160000000),((811906523:ℚ)/1032500000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((23145323:ℚ)/125000000),((-1887395881485280560030859367626609551516752795755127:ℚ)/97210230078125000000000000000000000000000000000000000),((-1641170802642093768648133:ℚ)/9241600000000000000000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((7588893447:ℚ)/10000000000),((7876665983:ℚ)/10000000000),((88597827917:ℚ)/129600000000),((25069997949:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((540693009:ℚ)/10000000000),((-9295957086828348141517497979073090381932697308586457949:ℚ)/503884800000000000000000000000000000000000000000000000000),((-41039784532138277147211493:ℚ)/231040000000000000000000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((7826499241:ℚ)/10000000000),((4888649819:ℚ)/5000000000),((91211491651:ℚ)/160000000000),((5128649819:ℚ)/5400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-41116900591714679920900851312445028048207631098860133443:ℚ)/4800000000000000000000000000000000000000000000000000000000),((-2842159:ℚ)/16000000)⟩
theorem valid15 : Valid tenth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((2431791149:ℚ)/2500000000),((6789021671:ℚ)/5000000000),((9343234213:ℚ)/18400000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-3507070621382077601652163659479181:ℚ)/1557376000000000000000000000000000000),((-2842159:ℚ)/16000000)⟩
theorem valid16 : Valid tenth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound tenth nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC28
#check @N11Formalization.C450TenthGroupedC28.bound
#print axioms N11Formalization.C450TenthGroupedC28.valid0
#print axioms N11Formalization.C450TenthGroupedC28.valid1
#print axioms N11Formalization.C450TenthGroupedC28.valid2
#print axioms N11Formalization.C450TenthGroupedC28.valid3
#print axioms N11Formalization.C450TenthGroupedC28.valid4
#print axioms N11Formalization.C450TenthGroupedC28.valid5
#print axioms N11Formalization.C450TenthGroupedC28.valid6
#print axioms N11Formalization.C450TenthGroupedC28.valid7
#print axioms N11Formalization.C450TenthGroupedC28.valid8
#print axioms N11Formalization.C450TenthGroupedC28.valid9
#print axioms N11Formalization.C450TenthGroupedC28.valid10
#print axioms N11Formalization.C450TenthGroupedC28.valid11
#print axioms N11Formalization.C450TenthGroupedC28.valid12
#print axioms N11Formalization.C450TenthGroupedC28.valid13
#print axioms N11Formalization.C450TenthGroupedC28.valid14
#print axioms N11Formalization.C450TenthGroupedC28.valid15
#print axioms N11Formalization.C450TenthGroupedC28.valid16
#print axioms N11Formalization.C450TenthGroupedC28.bound
#print axioms N11Formalization.C450TenthGroupedC28.endpoint_checks
