import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((552407303:ℚ)/1000000000),((3038395151:ℚ)/5000000000),((8333294939:ℚ)/10680000000),((24308766057:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7570695953:ℚ)/10000000000),((-844226401340990766777974168164331479:ℚ)/9517081500000000000000000000000000000),((-1382069738159960539267455217:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((2999925917:ℚ)/5000000000),((789343127:ℚ)/1250000000),((44759036921:ℚ)/55300000000),((2095133963:ℚ)/2225000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3304385291:ℚ)/5000000000),((-162744516520131695152691322575278709908492499766986738693:ℚ)/1585428534375000000000000000000000000000000000000000000000),((-85377876475072586531778593:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((6237701009:ℚ)/10000000000),((5119273:ℚ)/7812500),((92610113117:ℚ)/114400000000),((40584911:ℚ)/43203125),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((760091859:ℚ)/1250000000),((-480796116213059035139631903974623785787669505470045904787:ℚ)/4678731200000000000000000000000000000000000000000000000000),((-3295832866507558232893:ℚ)/9025000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((6475526939:ℚ)/10000000000),((266864849:ℚ)/400000000),((95701850207:ℚ)/116300000000),((2111253943:ℚ)/2288000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((688650647:ℚ)/1250000000),((-402032732676607790689098269081923803747450388725124523219:ℚ)/3686807219531250000000000000000000000000000000000000000000),((-8588276523220520982615217:ℚ)/23658496000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6594431901:ℚ)/10000000000),((3395283253:ℚ)/5000000000),((32415871571:ℚ)/39400000000),((26806982771:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5202631253:ℚ)/10000000000),((-15619057641732897117454196926850589876107440600609856447:ℚ)/143350743750000000000000000000000000000000000000000000000),((-1333850914260563210413372553:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((209791621:ℚ)/312500000),((3454752797:ℚ)/5000000000),((3087291073:ℚ)/3753125000),((9074423193:ℚ)/9850000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4878703169:ℚ)/10000000000),((-53959228091583672363026537253134071515903829809306901:ℚ)/495621757793426513671875000000000000000000000000000000),((-1325771245599526210008532953:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((6832227089:ℚ)/10000000000),((7028438779:ℚ)/10000000000),((100338952157:ℚ)/122000000000),((55279071453:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4533675107:ℚ)/10000000000),((-617335360526780526332487347848500622047096221734202882083:ℚ)/5674525000000000000000000000000000000000000000000000000000),((-5270716732088227376688425897:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((278044711:ℚ)/400000000),((7147366333:ℚ)/10000000000),((4075381243:ℚ)/4956000000),((56111564331:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2081136953:ℚ)/5000000000),((-1148746903272163662011269055687505941815874846951573:ℚ)/10566749550000000000000000000000000000000000000000000),((-5238298839531319742671743513:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((7070004139:ℚ)/10000000000),((7266288511:ℚ)/10000000000),((103430053807:ℚ)/125800000000),((18981339859:ℚ)/20650000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((751330777:ℚ)/2000000000),((-660055612719402871414265102505555967466825322912264897:ℚ)/6075639379882812500000000000000000000000000000000000000),((-5205831242322489052175120657:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((898610797:ℚ)/1250000000),((1876029423:ℚ)/2500000000),((13121940361:ℚ)/16200000000),((14652205961:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((3304201849:ℚ)/10000000000),((-50730120907944862093889134596125221358932858535865677:ℚ)/492075000000000000000000000000000000000000000000000000),((-963890006343306120839090579:ℚ)/2772480000000000000000000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((7426639201:ℚ)/10000000000),((8455261337:ℚ)/10000000000),((108066309613:ℚ)/144800000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((2139994567:ℚ)/10000000000),((-135722689809392583221695696762605788423515395297515284009:ℚ)/1778922300000000000000000000000000000000000000000000000000),((-354186259:ℚ)/1024000000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((8377517623:ℚ)/10000000000),((9406187369:ℚ)/10000000000),((120427729099:ℚ)/160000000000),((71923311583:ℚ)/72400000000),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-252948048473917066304399708406282636649831198835700056461:ℚ)/3200000000000000000000000000000000000000000000000000000000),((-354186259:ℚ)/1024000000)⟩
theorem valid11 : Valid source20 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source20 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((1865645791:ℚ)/2000000000),((13208615373:ℚ)/10000000000),((26557395283:ℚ)/44160000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-211212115159635916760388639899962079:ℚ)/10764582912000000000000000000000000000),((-354186259:ℚ)/1024000000)⟩
theorem valid12 : Valid source20 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source20 nn0 nn1 Qcell ((629:ℚ)/800) ((181:ℚ)/200) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source20 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source20 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC30
#check @N11Formalization.C450Source20GroupedC30.bound
#print axioms N11Formalization.C450Source20GroupedC30.valid0
#print axioms N11Formalization.C450Source20GroupedC30.valid1
#print axioms N11Formalization.C450Source20GroupedC30.valid2
#print axioms N11Formalization.C450Source20GroupedC30.valid3
#print axioms N11Formalization.C450Source20GroupedC30.valid4
#print axioms N11Formalization.C450Source20GroupedC30.valid5
#print axioms N11Formalization.C450Source20GroupedC30.valid6
#print axioms N11Formalization.C450Source20GroupedC30.valid7
#print axioms N11Formalization.C450Source20GroupedC30.valid8
#print axioms N11Formalization.C450Source20GroupedC30.valid9
#print axioms N11Formalization.C450Source20GroupedC30.valid10
#print axioms N11Formalization.C450Source20GroupedC30.valid11
#print axioms N11Formalization.C450Source20GroupedC30.valid12
#print axioms N11Formalization.C450Source20GroupedC30.bound
#print axioms N11Formalization.C450Source20GroupedC30.endpoint_checks
