import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((31026217:ℚ)/50000000),((672581697:ℚ)/1000000000),((-160581697:ℚ)/4960000000),((753993:ℚ)/16000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1538773689:ℚ)/2500000000),((1061404329640420090309279057:ℚ)/15872000000000000000000000000),((-1610484796384611537849:ℚ)/18483200000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((1336581793:ℚ)/2000000000),((6845167461:ℚ)/10000000000),((-1725167461:ℚ)/53400000000),((279806069:ℚ)/7120000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((620428283:ℚ)/1250000000),((218569201396089172978133023751851703514348361485346171:ℚ)/3383851200000000000000000000000000000000000000000000000),((-2926810761158789130540009:ℚ)/29573120000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((6802266659:ℚ)/10000000000),((435281073:ℚ)/625000000),((-115281073:ℚ)/3396875000),((4077733341:ℚ)/108700000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((23114323:ℚ)/50000000),((16123779402202437038739837253064619209779762471283304217:ℚ)/250852637304687500000000000000000000000000000000000000000),((-75358968173368873545606321:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((3460801659:ℚ)/5000000000),((1416761431:ℚ)/2000000000),((-392761431:ℚ)/11060000000),((1979198341:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2128652633:ℚ)/5000000000),((61150198601646149776191313645432848819917811065374009:ℚ)/955653125000000000000000000000000000000000000000000000),((-19387025781982954728936321:ℚ)/184832000000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((352046001:ℚ)/500000000),((3601549207:ℚ)/5000000000),((-347183069:ℚ)/9375000000),((191953999:ℚ)/5625000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1929808291:ℚ)/5000000000),((35443264352590015255652341129143420120689894812019723:ℚ)/556182861328125000000000000000000000000000000000000000),((-199344233111105521400841:ℚ)/1848320000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((7160217767:ℚ)/10000000000),((7322371871:ℚ)/10000000000),((-2202371871:ℚ)/57200000000),((3719782233:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1709282587:ℚ)/5000000000),((74261319858084987044768600829125949264916746109623372741:ℚ)/1169682800000000000000000000000000000000000000000000000000),((-81927756508965728710241049:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((7279497497:ℚ)/10000000000),((7441628391:ℚ)/10000000000),((-2321628391:ℚ)/58150000000),((3600502503:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1457243381:ℚ)/5000000000),((77759508508221298603755300620193827228863287525905154859:ℚ)/1228935739843750000000000000000000000000000000000000000000),((-84118309759642889952124569:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((7398760087:ℚ)/10000000000),((3840046907:ℚ)/5000000000),((-1280046907:ℚ)/29550000000),((3481239913:ℚ)/118200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((115318307:ℚ)/500000000),((979618533715388484624261370656765937540719791526960778183:ℚ)/15481880325000000000000000000000000000000000000000000000000),((-86309368739602462204137529:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((7637237073:ℚ)/10000000000),((8156853879:ℚ)/10000000000),((-3036853879:ℚ)/61000000000),((3242762927:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((89826258797001445007679955935683014476698525372439811779:ℚ)/1418631250000000000000000000000000000000000000000000000000),((-31166327:ℚ)/256000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((811401821:ℚ)/1000000000),((2012443059:ℚ)/2000000000),((-988443059:ℚ)/12960000000),((10244377:ℚ)/480000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((4209706210129714820509434543000918011616584293463:ℚ)/64800000000000000000000000000000000000000000000000),((-31166327:ℚ)/256000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((1001944373:ℚ)/1000000000),((866781143:ℚ)/625000000),((-546781143:ℚ)/5000000000),((86055627:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((36511061590143424652151999481562693:ℚ)/512000000000000000000000000000000000),((-31166327:ℚ)/256000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC15
#check @N11Formalization.C450Source18GroupedC15.bound
#print axioms N11Formalization.C450Source18GroupedC15.valid0
#print axioms N11Formalization.C450Source18GroupedC15.valid1
#print axioms N11Formalization.C450Source18GroupedC15.valid2
#print axioms N11Formalization.C450Source18GroupedC15.valid3
#print axioms N11Formalization.C450Source18GroupedC15.valid4
#print axioms N11Formalization.C450Source18GroupedC15.valid5
#print axioms N11Formalization.C450Source18GroupedC15.valid6
#print axioms N11Formalization.C450Source18GroupedC15.valid7
#print axioms N11Formalization.C450Source18GroupedC15.valid8
#print axioms N11Formalization.C450Source18GroupedC15.valid9
#print axioms N11Formalization.C450Source18GroupedC15.valid10
#print axioms N11Formalization.C450Source18GroupedC15.bound
#print axioms N11Formalization.C450Source18GroupedC15.endpoint_checks
