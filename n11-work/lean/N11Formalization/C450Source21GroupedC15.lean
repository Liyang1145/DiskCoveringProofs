import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((3099186883:ℚ)/5000000000),((3363820493:ℚ)/5000000000),((-323820493:ℚ)/24800000000),((3300813117:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3085366403:ℚ)/5000000000),((3276671155072548496784417033937851089:ℚ)/30505984000000000000000000000000000000),((-557938855144468556535561187:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((834634393:ℚ)/1250000000),((3483389589:ℚ)/5000000000),((-443389589:ℚ)/26700000000),((255121869:ℚ)/4450000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((497952137:ℚ)/1000000000),((171748817613007204889665428566831444145919773830492353:ℚ)/1652271093750000000000000000000000000000000000000000000),((-39000580991710907539810267:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((1729058261:ℚ)/2500000000),((7086306363:ℚ)/10000000000),((-1006306363:ℚ)/55300000000),((1470941739:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((427438301:ℚ)/1000000000),((1936150786154930798502211422617770717212394125697553347:ℚ)/18874149218750000000000000000000000000000000000000000000),((-164270762481893319445533043:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((7035769573:ℚ)/10000000000),((7205807487:ℚ)/10000000000),((-1125807487:ℚ)/56250000000),((5764230427:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((775515803:ℚ)/2000000000),((302980695977832210993930542148959826440433167522619060071:ℚ)/2966308593750000000000000000000000000000000000000000000000),((-2694521318483425378333972307:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((286211189:ℚ)/400000000),((3662641921:ℚ)/5000000000),((-56603811:ℚ)/2600000000),((225788811:ℚ)/4576000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3437894283:ℚ)/10000000000),((15232631147490694560147233471346036547319914836773469:ℚ)/149719398400000000000000000000000000000000000000000000),((-4417182706826137972449843:ℚ)/23658496000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((909345601:ℚ)/1250000000),((3722368319:ℚ)/5000000000),((-682368319:ℚ)/29075000000),((690654399:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((587216203:ℚ)/2000000000),((486683028727575767249230344105747725260623125226359969:ℚ)/4800530233764648437500000000000000000000000000000000000),((-44171664317145672924300683:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((3697113023:ℚ)/5000000000),((3841788003:ℚ)/5000000000),((-801788003:ℚ)/29550000000),((2702886977:ℚ)/59100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2332320341:ℚ)/10000000000),((130780831444015982986719621957583488613408117839624234647:ℚ)/1290156693750000000000000000000000000000000000000000000000),((-723315986024894080838656907:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((1526616299:ℚ)/2000000000),((2040254327:ℚ)/2500000000),((-520254327:ℚ)/15250000000),((1033383701:ℚ)/24400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2301919666419601427290351144992427988745424396081871059:ℚ)/22698100000000000000000000000000000000000000000000000000),((-41655533:ℚ)/204800000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((1013819011:ℚ)/1250000000),((10068450233:ℚ)/10000000000),((-147720379:ℚ)/2400000000),((21710407:ℚ)/600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((8776300779519663073368502874063674522363174116913:ℚ)/84375000000000000000000000000000000000000000000000),((-41655533:ℚ)/204800000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((5009037017:ℚ)/5000000000),((6938577503:ℚ)/5000000000),((-3898577503:ℚ)/40000000000),((1390962983:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((14663386618950299456526161801273290011:ℚ)/128000000000000000000000000000000000000),((-41655533:ℚ)/204800000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
private theorem node0_2 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source21 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_10
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_10
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9]
theorem packet_count : packets.length = 10 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC15
#check @N11Formalization.C450Source21GroupedC15.bound
#print axioms N11Formalization.C450Source21GroupedC15.valid0
#print axioms N11Formalization.C450Source21GroupedC15.valid1
#print axioms N11Formalization.C450Source21GroupedC15.valid2
#print axioms N11Formalization.C450Source21GroupedC15.valid3
#print axioms N11Formalization.C450Source21GroupedC15.valid4
#print axioms N11Formalization.C450Source21GroupedC15.valid5
#print axioms N11Formalization.C450Source21GroupedC15.valid6
#print axioms N11Formalization.C450Source21GroupedC15.valid7
#print axioms N11Formalization.C450Source21GroupedC15.valid8
#print axioms N11Formalization.C450Source21GroupedC15.valid9
#print axioms N11Formalization.C450Source21GroupedC15.bound
#print axioms N11Formalization.C450Source21GroupedC15.endpoint_checks
