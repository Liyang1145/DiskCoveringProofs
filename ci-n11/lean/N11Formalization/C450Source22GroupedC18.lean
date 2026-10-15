import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((3019365271:ℚ)/5000000000),((6577075149:ℚ)/10000000000),((9419365271:ℚ)/53400000000),((13297075149:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6524975927:ℚ)/10000000000),((3893321313777745872252092698124623728649:ℚ)/35076469248000000000000000000000000000000),((-761793549318155717870725343:ℚ)/2772480000000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((3258883773:ℚ)/5000000000),((6816233049:ℚ)/10000000000),((1379840539:ℚ)/7900000000),((4512077683:ℚ)/17800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5402094189:ℚ)/10000000000),((34707924841945191764659670839292440343612878054866983528977:ℚ)/329978364675000000000000000000000000000000000000000000000000),((-813266360715470259669625943:ℚ)/2772480000000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((844634447:ℚ)/1250000000),((3467884789:ℚ)/5000000000),((814878149:ℚ)/4687500000),((6827884789:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1188613737:ℚ)/2500000000),((8738071814855914164644617452265106908831978136415600139:ℚ)/84933671484375000000000000000000000000000000000000000000),((-69912028017974131343549701:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((859585411:ℚ)/1250000000),((705527973:ℚ)/1000000000),((2459585411:ℚ)/14300000000),((459175991:ℚ)/1875000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2199118429:ℚ)/5000000000),((43125559933505611698213070790404283906723793971022798367:ℚ)/421236419677734375000000000000000000000000000000000000000),((-8510816126242162368345647:ℚ)/27724800000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((6996262209:ℚ)/10000000000),((7174764813:ℚ)/10000000000),((19796262209:ℚ)/116300000000),((13894764813:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4012824763:ℚ)/10000000000),((20158171669491646598941614590428782708641426148450633158785901:ℚ)/197759586889150000000000000000000000000000000000000000000000000),((-863192530050143015078671967:ℚ)/2772480000000000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((1778953443:ℚ)/2500000000),((7294226051:ℚ)/10000000000),((4978953443:ℚ)/29550000000),((14014226051:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((897196427:ℚ)/2500000000),((1816067906581598487102390182223292547772122190137279982990841:ℚ)/17885162672848535156250000000000000000000000000000000000000000),((-291759083471727654702916181:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((452208707:ℚ)/625000000),((15066163:ℚ)/20000000),((1252208707:ℚ)/7625000000),((28506163:ℚ)/118200000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((9719741:ℚ)/31250000),((96449185187368191912751488893966152626439818762037:ℚ)/944394699825000000000000000000000000000000000000000),((-1181164849954633555189:ℚ)/3696640000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((7474317249:ℚ)/10000000000),((8010552093:ℚ)/10000000000),((20274317249:ℚ)/129600000000),((14730552093:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((364230543:ℚ)/2000000000),((120096871778758756039253965470765757442511413867728539758549:ℚ)/1163454953906250000000000000000000000000000000000000000000000),((-80002757680621731:ℚ)/243200000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((198800273:ℚ)/250000000),((9918074039:ℚ)/10000000000),((518800273:ℚ)/4000000000),((16638074039:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((17564697679612134906773201761455253087732956545454651341:ℚ)/159432300000000000000000000000000000000000000000000000000),((-21380993:ℚ)/64000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((9860210733:ℚ)/10000000000),((6863441407:ℚ)/5000000000),((22660210733:ℚ)/220800000000),((10223441407:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((4976381121733513378965319595957745564517:ℚ)/38088000000000000000000000000000000000000),((-21380993:ℚ)/64000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
private theorem node0_2 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source22 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_10
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_10
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9]
theorem packet_count : packets.length = 10 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC18
#check @N11Formalization.C450Source22GroupedC18.bound
#print axioms N11Formalization.C450Source22GroupedC18.valid0
#print axioms N11Formalization.C450Source22GroupedC18.valid1
#print axioms N11Formalization.C450Source22GroupedC18.valid2
#print axioms N11Formalization.C450Source22GroupedC18.valid3
#print axioms N11Formalization.C450Source22GroupedC18.valid4
#print axioms N11Formalization.C450Source22GroupedC18.valid5
#print axioms N11Formalization.C450Source22GroupedC18.valid6
#print axioms N11Formalization.C450Source22GroupedC18.valid7
#print axioms N11Formalization.C450Source22GroupedC18.valid8
#print axioms N11Formalization.C450Source22GroupedC18.valid9
#print axioms N11Formalization.C450Source22GroupedC18.bound
#print axioms N11Formalization.C450Source22GroupedC18.endpoint_checks
