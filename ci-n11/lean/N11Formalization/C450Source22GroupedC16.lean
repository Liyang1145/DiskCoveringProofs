import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC16
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((-1:ℚ)/16),(0:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/16),(0:ℚ),((307141661:ℚ)/500000000),((6677075149:ℚ)/10000000000),((6122924851:ℚ)/106800000000),((21:ℚ)/155),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1573981203:ℚ)/2500000000),((707516812668167382625948822129:ℚ)/5480698320000000000000000000000),((-10649603830122903:ℚ)/48640000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((3310967569:ℚ)/5000000000),((6916233049:ℚ)/10000000000),((5883766951:ℚ)/110600000000),((56:ℚ)/445),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((205174567:ℚ)/400000000),((2304671749328880461608432344872709371043163:ℚ)/18478788421800000000000000000000000000000000),((-6116719395511073:ℚ)/25600000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/16),(0:ℚ),((6861272201:ℚ)/10000000000),((3517884789:ℚ)/5000000000),((2882115211:ℚ)/56250000000),((48:ℚ)/395),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4445623387:ℚ)/10000000000),((959680283177612705303390715154438991571539:ℚ)/7800031054687500000000000000000000000000000),((-242148286760783323:ℚ)/972800000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/16),(0:ℚ),((6980893677:ℚ)/10000000000),((715527973:ℚ)/1000000000),((564472027:ℚ)/11440000000),((224:ℚ)/1875),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4064284043:ℚ)/10000000000),((845592662110859634031512446680485142417207:ℚ)/6901537500000000000000000000000000000000000),((-247002851986142471:ℚ)/972800000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((887560737:ℚ)/1250000000),((7274764813:ℚ)/10000000000),((5525235187:ℚ)/116300000000),((84:ℚ)/715),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((911443953:ℚ)/2500000000),((12069493470971849975677130188153830051528791:ℚ)/98879793444575000000000000000000000000000000),((-1656948880807729:ℚ)/6400000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((7220050313:ℚ)/10000000000),((7394226051:ℚ)/10000000000),((5405773949:ℚ)/118200000000),((672:ℚ)/5815),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((127015691:ℚ)/400000000),((2227984582213612115801974582748744419732182449:ℚ)/18314406576996900000000000000000000000000000000),((-256708479498542299:ℚ)/972800000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/16),(0:ℚ),((3669794143:ℚ)/5000000000),((15266163:ℚ)/20000000),((10333837:ℚ)/244000000),((112:ℚ)/985),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2625345137:ℚ)/10000000000),((68095149093782176737803757355025340877:ℚ)/559641303600000000000000000000000000000),((-130779827972391389:ℚ)/486400000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/16),(0:ℚ),((3789294953:ℚ)/5000000000),((8110552093:ℚ)/10000000000),((4689447907:ℚ)/129600000000),((168:ℚ)/1525),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((9384897:ℚ)/125000000),((232065645962587085703776533045021732178927:ℚ)/1906204596480000000000000000000000000000000),((-135629496242897019:ℚ)/486400000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/16),(0:ℚ),((503520419:ℚ)/625000000),((10018074039:ℚ)/10000000000),((2781925961:ℚ)/160000000000),((14:ℚ)/135),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((234033204464070826714112343162270640289251:ℚ)/1889568000000000000000000000000000000000000),((-35806299:ℚ)/128000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/16),(0:ℚ),((9964657543:ℚ)/10000000000),((1382701111:ℚ)/1000000000),((-102701111:ℚ)/16000000000),((21:ℚ)/250),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1097357209154507:ℚ)/8000000000000000),((-35806299:ℚ)/128000000)⟩
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
end N11Formalization.C450Source22GroupedC16
#check @N11Formalization.C450Source22GroupedC16.bound
#print axioms N11Formalization.C450Source22GroupedC16.valid0
#print axioms N11Formalization.C450Source22GroupedC16.valid1
#print axioms N11Formalization.C450Source22GroupedC16.valid2
#print axioms N11Formalization.C450Source22GroupedC16.valid3
#print axioms N11Formalization.C450Source22GroupedC16.valid4
#print axioms N11Formalization.C450Source22GroupedC16.valid5
#print axioms N11Formalization.C450Source22GroupedC16.valid6
#print axioms N11Formalization.C450Source22GroupedC16.valid7
#print axioms N11Formalization.C450Source22GroupedC16.valid8
#print axioms N11Formalization.C450Source22GroupedC16.valid9
#print axioms N11Formalization.C450Source22GroupedC16.bound
#print axioms N11Formalization.C450Source22GroupedC16.endpoint_checks
