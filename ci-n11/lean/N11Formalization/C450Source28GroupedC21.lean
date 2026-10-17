import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/4),((5:ℚ)/16),((5777032379:ℚ)/10000000000),((6098254971:ℚ)/10000000000),((9937032379:ℚ)/25750000000),((9554254971:ℚ)/19840000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7072741781:ℚ)/10000000000),((-655430630058471500677447256806609190443:ℚ)/20712830992384000000000000000000000000000),((-1155126832022572792324111817:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((6017727177:ℚ)/10000000000),((633860781:ℚ)/1000000000),((10177727177:ℚ)/26700000000),((979460781:ℚ)/2060000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((6570357211:ℚ)/10000000000),((-53392861186907973588063098807830790464746755851601199:ℚ)/1690525501367187500000000000000000000000000000000000000),((-11722011186112850725743257:ℚ)/29573120000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((391136897:ℚ)/625000000),((3229354071:ℚ)/5000000000),((651136897:ℚ)/1698437500),((1652451357:ℚ)/3560000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1206676511:ℚ)/2000000000),((-11869598565218582094512221209282753216043814176415526079247:ℚ)/333187806544400000000000000000000000000000000000000000000000),((-298966064227221396428353217:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((6378342857:ℚ)/10000000000),((205586291:ℚ)/312500000),((1505477551:ℚ)/3950000000),((313586291:ℚ)/679375000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((5748835267:ℚ)/10000000000),((-81076660998466045315723430428256813042712922345355147:ℚ)/2293317347781085968017578125000000000000000000000000000),((-1175834892277610543985897:ℚ)/2888000000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((6498446347:ℚ)/10000000000),((3349384881:ℚ)/5000000000),((3552815449:ℚ)/9375000000),((5077384881:ℚ)/11060000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5451322361:ℚ)/10000000000),((-127025227226519669974277425696002588963380579171702231:ℚ)/3623836650000000000000000000000000000000000000000000000),((-303027679068958621244288657:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((3309251681:ℚ)/5000000000),((1363747153:ℚ)/2000000000),((489931971:ℚ)/1300000000),((2054947153:ℚ)/4500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5138558111:ℚ)/10000000000),((-3342161155300166791962732292617347658962453167752257267:ℚ)/96250781250000000000000000000000000000000000000000000000),((-48801277843182422137364433:ℚ)/118292480000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((6738516267:ℚ)/10000000000),((1387732289:ℚ)/2000000000),((10898516267:ℚ)/29075000000),((2078932289:ℚ)/4576000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4807531611:ℚ)/10000000000),((-20878597774076114383592712582269723980159439767323931477073:ℚ)/607517450923468800000000000000000000000000000000000000000000),((-49112757025415771862988977:ℚ)/118292480000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((6858487269:ℚ)/10000000000),((7058548783:ℚ)/10000000000),((11018487269:ℚ)/29550000000),((10514548783:ℚ)/23260000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4454136361:ℚ)/10000000000),((-25933754529645551355486560415951847652327939717612252516037:ℚ)/763100274041537500000000000000000000000000000000000000000000),((-1235471941191947948122000593:ℚ)/2957312000000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((6978418429:ℚ)/10000000000),((7298215731:ℚ)/10000000000),((11138418429:ℚ)/30500000000),((3584738577:ℚ)/7880000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1018128649:ℚ)/2500000000),((-339958939341801492229547695008251782474340377426869996003:ℚ)/11379373173200000000000000000000000000000000000000000000000),((-1235086543462494979254596057:ℚ)/2957312000000000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((7218168813:ℚ)/10000000000),((7777163681:ℚ)/10000000000),((11378168813:ℚ)/32400000000),((11233163681:ℚ)/24400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((198956981:ℚ)/625000000),((-1113310590800685462874975246388868214556375658643238697857:ℚ)/49640744700000000000000000000000000000000000000000000000000),((-51199566045205707:ℚ)/121600000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((1539453717:ℚ)/2000000000),((4844585411:ℚ)/5000000000),((2371453717:ℚ)/8000000000),((6572585411:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((130364273160523801901331990700289:ℚ)/15000000000000000000000000000000000),((-448016031:ℚ)/1024000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((9609736109:ℚ)/10000000000),((13503211837:ℚ)/10000000000),((13769736109:ℚ)/55200000000),((16959211837:ℚ)/32000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1621427607776170496466179:ℚ)/31740000000000000000000000),((-448016031:ℚ)/1024000000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC21
#check @N11Formalization.C450Source28GroupedC21.bound
#print axioms N11Formalization.C450Source28GroupedC21.valid0
#print axioms N11Formalization.C450Source28GroupedC21.valid1
#print axioms N11Formalization.C450Source28GroupedC21.valid2
#print axioms N11Formalization.C450Source28GroupedC21.valid3
#print axioms N11Formalization.C450Source28GroupedC21.valid4
#print axioms N11Formalization.C450Source28GroupedC21.valid5
#print axioms N11Formalization.C450Source28GroupedC21.valid6
#print axioms N11Formalization.C450Source28GroupedC21.valid7
#print axioms N11Formalization.C450Source28GroupedC21.valid8
#print axioms N11Formalization.C450Source28GroupedC21.valid9
#print axioms N11Formalization.C450Source28GroupedC21.valid10
#print axioms N11Formalization.C450Source28GroupedC21.valid11
#print axioms N11Formalization.C450Source28GroupedC21.bound
#print axioms N11Formalization.C450Source28GroupedC21.endpoint_checks
