import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((739108797:ℚ)/1250000000),((1611814239:ℚ)/2500000000),((995108797:ℚ)/2670000000),((6195442717:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1698263623:ℚ)/2500000000),((536346444751065387925661620474634715947:ℚ)/16990164792000000000000000000000000000000),((-1515834931913362744479293:ℚ)/5776000000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((1278033483:ℚ)/2000000000),((6685713927:ℚ)/10000000000),((1687633483:ℚ)/4424000000),((25497141781:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2860078753:ℚ)/5000000000),((11865441348264758268216480719012362545744527171657721720075211:ℚ)/436561376465025000000000000000000000000000000000000000000000000),((-24992525435846407722600557:ℚ)/92416000000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((662869677:ℚ)/1000000000),((1731026741:ℚ)/2500000000),((867669677:ℚ)/2288000000),((6553080223:ℚ)/13825000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((2555602643:ℚ)/5000000000),((622790990921589696577747453322832520476102269304597039:ℚ)/23488161962890625000000000000000000000000000000000000000),((-1583265838380058623541973:ℚ)/5776000000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((274686293:ℚ)/400000000),((176082037:ℚ)/250000000),((356606293:ℚ)/930400000),((664246111:ℚ)/1430000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4427583513:ℚ)/10000000000),((229838146198997722474133660063095914571563040159633433281:ℚ)/9269980635428906250000000000000000000000000000000000000000),((-16062362180888298332877:ℚ)/57760000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((6986363927:ℚ)/10000000000),((7162442277:ℚ)/10000000000),((9034363927:ℚ)/23640000000),((26927326831:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4046038607:ℚ)/10000000000),((146614125229300914760348678150288632444559362409746494454123:ℚ)/5961720890949511718750000000000000000000000000000000000000000),((-25868300894030215777472757:ℚ)/92416000000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((888194471:ℚ)/1250000000),((7281590011:ℚ)/10000000000),((1144194471:ℚ)/3002500000),((27284770033:ℚ)/59100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1813510213:ℚ)/5000000000),((68158101381543278036530493746870121794503067141101665221990543:ℚ)/2791384957832540625000000000000000000000000000000000000000000000),((-26036299370995085866202293:ℚ)/92416000000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((7224733553:ℚ)/10000000000),((7400725297:ℚ)/10000000000),((9272733553:ℚ)/24400000000),((27642175891:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1577798337:ℚ)/5000000000),((61102507718203285999670399769132469810359839806007666687823:ℚ)/2517959421609765625000000000000000000000000000000000000000000),((-26203776097999869953061597:ℚ)/92416000000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((917987243:ℚ)/1250000000),((7638960791:ℚ)/10000000000),((1173987243:ℚ)/3145000000),((28356882373:ℚ)/61000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((2603405979:ℚ)/10000000000),((1770331520240509664091573522677482726859611574062726762170961:ℚ)/70158585797656250000000000000000000000000000000000000000000000),((-4333770062350703:ℚ)/15200000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((7582188987:ℚ)/10000000000),((3938576483:ℚ)/5000000000),((9630188987:ℚ)/25920000000),((14535729449:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((171189599:ℚ)/2500000000),((15948159744383644355730230026676526297504017536899893223013:ℚ)/637796319542578125000000000000000000000000000000000000000000),((-35192070545296127:ℚ)/121600000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((3910216711:ℚ)/5000000000),((1956300579:ℚ)/2000000000),((4934216711:ℚ)/16000000000),((6956901737:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((34246592715543937960742801180948657:ℚ)/960000000000000000000000000000000000),((-9271337:ℚ)/32000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((972511147:ℚ)/1000000000),((6793301097:ℚ)/5000000000),((392437049:ℚ)/1472000000),((23099903291:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((54149563109618639035209:ℚ)/1083392000000000000000000),((-9271337:ℚ)/32000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source18 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC22
#check @N11Formalization.C450Source18GroupedC22.bound
#print axioms N11Formalization.C450Source18GroupedC22.valid0
#print axioms N11Formalization.C450Source18GroupedC22.valid1
#print axioms N11Formalization.C450Source18GroupedC22.valid2
#print axioms N11Formalization.C450Source18GroupedC22.valid3
#print axioms N11Formalization.C450Source18GroupedC22.valid4
#print axioms N11Formalization.C450Source18GroupedC22.valid5
#print axioms N11Formalization.C450Source18GroupedC22.valid6
#print axioms N11Formalization.C450Source18GroupedC22.valid7
#print axioms N11Formalization.C450Source18GroupedC22.valid8
#print axioms N11Formalization.C450Source18GroupedC22.valid9
#print axioms N11Formalization.C450Source18GroupedC22.valid10
#print axioms N11Formalization.C450Source18GroupedC22.bound
#print axioms N11Formalization.C450Source18GroupedC22.endpoint_checks
