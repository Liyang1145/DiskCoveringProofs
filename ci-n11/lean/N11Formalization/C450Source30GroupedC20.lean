import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/16),((1:ℚ)/4),((1451854371:ℚ)/2500000000),((3066399781:ℚ)/5000000000),((8835563113:ℚ)/25750000000),((5386399781:ℚ)/12400000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((701098769:ℚ)/1000000000),((-16713307041804125183251258996617266988037987968903281147:ℚ)/106711621093750000000000000000000000000000000000000000000),((-3748541552931988197237727:ℚ)/11552000000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((6048762199:ℚ)/10000000000),((3186858329:ℚ)/5000000000),((36066286597:ℚ)/106800000000),((5506858329:ℚ)/12875000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((3251602769:ℚ)/5000000000),((-32334578034694930242646683216149651692315397927432897407:ℚ)/211490700000000000000000000000000000000000000000000000000),((-3792957544760411706967687:ℚ)/11552000000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((6289827123:ℚ)/10000000000),((6494083763:ℚ)/10000000000),((36789481369:ℚ)/108700000000),((11134083763:ℚ)/26700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5959621327:ℚ)/10000000000),((-1229239028871910491660622465605903178261118925976873124579:ℚ)/8027284393750000000000000000000000000000000000000000000000),((-15472948919406295474039183:ℚ)/46208000000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((6410264101:ℚ)/10000000000),((3307197103:ℚ)/5000000000),((37150792303:ℚ)/110600000000),((5627197103:ℚ)/13587500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2835561087:ℚ)/5000000000),((-20006743270477043258139172732534379801682468829442653853:ℚ)/132119044531250000000000000000000000000000000000000000000),((-3888846104852216993586263:ℚ)/11552000000000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((6530641921:ℚ)/10000000000),((3367325467:ℚ)/5000000000),((37511925763:ℚ)/112500000000),((5687325467:ℚ)/13825000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5369066271:ℚ)/10000000000),((-192865195700875850865631898236733949941028882282753571:ℚ)/1287460327148437500000000000000000000000000000000000000),((-3908831066774882309174623:ℚ)/11552000000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((332548183:ℚ)/500000000),((6854856689:ℚ)/10000000000),((1893644549:ℚ)/5720000000),((11494856689:ℚ)/28125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((505098537:ℚ)/1000000000),((-173402531461129181059966296156119367313751479868573719:ℚ)/1169682800000000000000000000000000000000000000000000000),((-826988109389817712943213:ℚ)/2432000000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((1354246437:ℚ)/2000000000),((6975014029:ℚ)/10000000000),((7646739311:ℚ)/23260000000),((11615014029:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((294599911:ℚ)/625000000),((-11542903889194736763510341166919227191251302842299330669:ℚ)/78651887350000000000000000000000000000000000000000000000),((-15787739085417852807151887:ℚ)/46208000000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((6891450169:ℚ)/10000000000),((221722667:ℚ)/312500000),((38594350507:ℚ)/118200000000),((366722667:ℚ)/908593750),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2176189549:ℚ)/5000000000),((-41667664778396664751110822703302101219546303209693737497:ℚ)/286701487500000000000000000000000000000000000000000000000),((-484015630028968185589:ℚ)/1410156250000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((7011620109:ℚ)/10000000000),((7335218687:ℚ)/10000000000),((38954860327:ℚ)/122000000000),((11975218687:ℚ)/29550000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((247548121:ℚ)/625000000),((-1599794730445694635968124099104764307005712330757916848493:ℚ)/11349050000000000000000000000000000000000000000000000000000),((-15782382108891365421985783:ℚ)/46208000000000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((3625912521:ℚ)/5000000000),((781494237:ℚ)/1000000000),((19837737563:ℚ)/64800000000),((1245494237:ℚ)/3050000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1519319409:ℚ)/5000000000),((-103574731224463257070574970935877068896432657274499091:ℚ)/777600000000000000000000000000000000000000000000000000),((-5223122527660087:ℚ)/15200000000000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((7731751677:ℚ)/10000000000),((9729300783:ℚ)/10000000000),((41115255031:ℚ)/160000000000),((14369300783:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-2715080690646609032789825858891172715040318610224482043381:ℚ)/25600000000000000000000000000000000000000000000000000000000),((-2857097:ℚ)/8000000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((964672481:ℚ)/1000000000),((13546078659:ℚ)/10000000000),((4686017443:ℚ)/22080000000),((18186078659:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-148618745078195382040643722583067880935915271960417633:ℚ)/1868851200000000000000000000000000000000000000000000000),((-2857097:ℚ)/8000000)⟩
theorem valid11 : Valid source30 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC20
#check @N11Formalization.C450Source30GroupedC20.bound
#print axioms N11Formalization.C450Source30GroupedC20.valid0
#print axioms N11Formalization.C450Source30GroupedC20.valid1
#print axioms N11Formalization.C450Source30GroupedC20.valid2
#print axioms N11Formalization.C450Source30GroupedC20.valid3
#print axioms N11Formalization.C450Source30GroupedC20.valid4
#print axioms N11Formalization.C450Source30GroupedC20.valid5
#print axioms N11Formalization.C450Source30GroupedC20.valid6
#print axioms N11Formalization.C450Source30GroupedC20.valid7
#print axioms N11Formalization.C450Source30GroupedC20.valid8
#print axioms N11Formalization.C450Source30GroupedC20.valid9
#print axioms N11Formalization.C450Source30GroupedC20.valid10
#print axioms N11Formalization.C450Source30GroupedC20.valid11
#print axioms N11Formalization.C450Source30GroupedC20.bound
#print axioms N11Formalization.C450Source30GroupedC20.endpoint_checks
