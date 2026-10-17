import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((2805913013:ℚ)/5000000000),((6166271067:ℚ)/10000000000),((10657739039:ℚ)/17800000000),((7574271067:ℚ)/9920000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7401043969:ℚ)/10000000000),((-27802198797325357888834827619844221:ℚ)/352484500000000000000000000000000000),((-682773241052751717505242431:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((1522389397:ℚ)/2500000000),((6405022267:ℚ)/10000000000),((17061504573:ℚ)/27650000000),((7813022267:ℚ)/10680000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6414022083:ℚ)/10000000000),((-3133404264536036152705201253555967583532446424727904389:ℚ)/33029761132812500000000000000000000000000000000000000000),((-685786966460274376165765631:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((9:ℚ)/16),((5:ℚ)/8),((6328281487:ℚ)/10000000000),((652436593:ℚ)/1000000000),((23464844461:ℚ)/37500000000),((793236593:ℚ)/1106000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((733608717:ℚ)/1250000000),((-311722117321070843350568890291208905555329487615094919:ℚ)/3051757812500000000000000000000000000000000000000000000),((-6872089143338254058238071:ℚ)/18483200000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((3223806101:ℚ)/5000000000),((6643689731:ℚ)/10000000000),((35734254909:ℚ)/57200000000),((2683896577:ℚ)/3750000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((348685973:ℚ)/625000000),((-2712749163398403065918990168447197030237226113067604087:ℚ)/26583700000000000000000000000000000000000000000000000000),((-686364834136228328574024719:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((656692349:ℚ)/1000000000),((6762994651:ℚ)/10000000000),((7254231141:ℚ)/11630000000),((8170994651:ℚ)/11440000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5274986613:ℚ)/10000000000),((-62630330222778910968977090785235118652456687531298637:ℚ)/614467869921875000000000000000000000000000000000000000),((-685465540487108928495548479:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((6686216313:ℚ)/10000000000),((688228161:ℚ)/1000000000),((24538648939:ℚ)/39400000000),((829028161:ℚ)/1163000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4954280241:ℚ)/10000000000),((-2431886092792778298389624706467762088918999848960374867:ℚ)/23891790625000000000000000000000000000000000000000000000),((-6845110528591940427871959:ℚ)/18483200000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((425343223:ℚ)/625000000),((1750387867:ℚ)/2500000000),((4668089007:ℚ)/7506250000),((2102387867:ℚ)/2955000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2306670639:ℚ)/5000000000),((-67160380048669919980699771574396202241505298208498311:ℚ)/660829010391235351562500000000000000000000000000000000),((-42718836840256523650487231:ℚ)/115520000000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((3462375049:ℚ)/5000000000),((7120805031:ℚ)/10000000000),((37881375441:ℚ)/61000000000),((8528805031:ℚ)/12010000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2123634199:ℚ)/5000000000),((-35982075263398029506042029897676070032559192618653784777:ℚ)/354657812500000000000000000000000000000000000000000000000),((-682436567329688646951974119:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((7043992689:ℚ)/10000000000),((7240043053:ℚ)/10000000000),((25611978067:ℚ)/41300000000),((8648043053:ℚ)/12200000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((3848862589:ℚ)/10000000000),((-2786538352040434425460267070365229101075981290807491051:ℚ)/27517576953125000000000000000000000000000000000000000000),((-681316602513883596290769711:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((7163220081:ℚ)/10000000000),((3679633123:ℚ)/5000000000),((77908980729:ℚ)/125800000000),((1461211041:ℚ)/2065000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((851690411:ℚ)/2500000000),((-18058173548969378217750387957768715116903590520245961:ℚ)/178695275878906250000000000000000000000000000000000000),((-170035377485837219563766991:ℚ)/462080000000000000000000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((7282432969:ℚ)/10000000000),((1899417693:ℚ)/2500000000),((26327298907:ℚ)/43200000000),((2251417693:ℚ)/3145000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((362626797:ℚ)/1250000000),((-147534027398592534462458620216670761572768375013393579:ℚ)/1555200000000000000000000000000000000000000000000000000),((-42213651261692573440331471:ℚ)/115520000000000000000000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((37604089:ℚ)/50000000),((9503353663:ℚ)/10000000000),((405636801:ℚ)/800000000),((10911353663:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1444773517:ℚ)/10000000000),((-1708502280241389209418715280003710779065869037673:ℚ)/50000000000000000000000000000000000000000000000000),((-223606751098003:ℚ)/608000000000000)⟩
theorem valid11 : Valid source23 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((1885275419:ℚ)/2000000000),((133100127:ℚ)/100000000),((6551826257:ℚ)/14720000000),((147180127:ℚ)/160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((39703209158851893086413:ℚ)/3385600000000000000000000),((-47176661:ℚ)/128000000)⟩
theorem valid12 : Valid source23 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source23 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((1239:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source23 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source23 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC26
#check @N11Formalization.C450Source23GroupedC26.bound
#print axioms N11Formalization.C450Source23GroupedC26.valid0
#print axioms N11Formalization.C450Source23GroupedC26.valid1
#print axioms N11Formalization.C450Source23GroupedC26.valid2
#print axioms N11Formalization.C450Source23GroupedC26.valid3
#print axioms N11Formalization.C450Source23GroupedC26.valid4
#print axioms N11Formalization.C450Source23GroupedC26.valid5
#print axioms N11Formalization.C450Source23GroupedC26.valid6
#print axioms N11Formalization.C450Source23GroupedC26.valid7
#print axioms N11Formalization.C450Source23GroupedC26.valid8
#print axioms N11Formalization.C450Source23GroupedC26.valid9
#print axioms N11Formalization.C450Source23GroupedC26.valid10
#print axioms N11Formalization.C450Source23GroupedC26.valid11
#print axioms N11Formalization.C450Source23GroupedC26.valid12
#print axioms N11Formalization.C450Source23GroupedC26.bound
#print axioms N11Formalization.C450Source23GroupedC26.endpoint_checks
