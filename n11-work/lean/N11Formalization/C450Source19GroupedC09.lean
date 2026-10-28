import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((1293454719:ℚ)/2000000000),((6767230781:ℚ)/10000000000),((-5407230781:ℚ)/12400000000),((-6750183033:ℚ)/20600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((172809867:ℚ)/312500000),((130644904521429857406283313200571130579907599271559147541:ℚ)/1693726850000000000000000000000000000000000000000000000000),((154495696719059152699623929:ℚ)/887193600000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((6705893907:ℚ)/10000000000),((215204111:ℚ)/312500000),((-172704111:ℚ)/402343750),((-35421257349:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4899540959:ℚ)/10000000000),((13880568420532954509781814449656708562365626225226772506249:ℚ)/185773479448437500000000000000000000000000000000000000000000),((3766268414672718698863171361:ℚ)/22179840000000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((341258671:ℚ)/500000000),((3502906297:ℚ)/5000000000),((-2822906297:ℚ)/6556250000),((-1812810697:ℚ)/5340000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4554819293:ℚ)/10000000000),((18632799847839240038711169912588940747469780521974837011:ℚ)/249585462337500000000000000000000000000000000000000000000),((3098283769757813134911283:ℚ)/18483200000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((6944433971:ℚ)/10000000000),((3532723023:ℚ)/5000000000),((-2852723023:ℚ)/6675000000),((-37091037797:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4183972339:ℚ)/10000000000),((599811117661866799753895089347686376661401739758050594413:ℚ)/8154609144973754882812500000000000000000000000000000000000),((1223144967533023808820555083:ℚ)/7393280000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((1751014363:ℚ)/2500000000),((7125074951:ℚ)/10000000000),((-5765074951:ℚ)/13468750000),((-9377100541:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1993241789:ℚ)/5000000000),((3975479456866163707105632163891771136483824178798554715193:ℚ)/54058743339160156250000000000000000000000000000000000000000),((75939902953290085390096347:ℚ)/462080000000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7063676563:ℚ)/10000000000),((7184699429:ℚ)/10000000000),((-5824699429:ℚ)/13587500000),((-37925735941:ℚ)/109650000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((755856337:ℚ)/2000000000),((54877041731775379599099069989175279900341116238518223633947:ℚ)/746370083525976562500000000000000000000000000000000000000000),((1206917076498740643848039947:ℚ)/7393280000000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((3561645709:ℚ)/5000000000),((1448863919:ℚ)/2000000000),((-392287973:ℚ)/913750000),((-19171519963:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3560666837:ℚ)/10000000000),((2662343059701633208707818833264920034785887280746509497257:ℚ)/36217133082128906250000000000000000000000000000000000000000),((299695210773481784460781003:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((448931383:ℚ)/625000000),((7303935559:ℚ)/10000000000),((-5943935559:ℚ)/13825000000),((-2422519681:ℚ)/6971875000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3328386117:ℚ)/10000000000),((5380192784210084782407311107229367491256853985262109651:ℚ)/73203853276050090789794921875000000000000000000000000000),((4650897402941621578074307:ℚ)/28880000000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/2),((-7:ℚ)/16),((565821:ℚ)/781250),((736354743:ℚ)/1000000000),((-600354743:ℚ)/1394375000),((-680166:ℚ)/1953125),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3079343431:ℚ)/10000000000),((119280085278772516817352736008506264712642807:ℚ)/1623266143724322319030761718750000000000000000),((1353222360104668589:ℚ)/8460937500000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((7302111537:ℚ)/10000000000),((7482759299:ℚ)/10000000000),((-6122759299:ℚ)/14062500000),((-39594780759:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2809078619:ℚ)/10000000000),((2089284997588851715384224286232555348802973498937756660191:ℚ)/28072387200000000000000000000000000000000000000000000000000),((3522848550882484618736516441:ℚ)/22179840000000000000000000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((7421305599:ℚ)/10000000000),((7721138247:ℚ)/10000000000),((-6361138247:ℚ)/14300000000),((-13476379731:ℚ)/39400000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2172792781:ℚ)/10000000000),((94668231249262054906459015882135593042430431667601403189:ℚ)/1242373112500000000000000000000000000000000000000000000000),((3473629006386610457653245689:ℚ)/22179840000000000000000000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/2),((-7:ℚ)/16),((1914912667:ℚ)/2500000000),((1591892431:ℚ)/2000000000),((-1319892431:ℚ)/2955000000),((-10524388669:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((7965603100012858219845883776565812494985378111372790371497:ℚ)/104801383593750000000000000000000000000000000000000000000000),((78473977:ℚ)/512000000)⟩
theorem valid11 : Valid source19 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((789794283:ℚ)/1000000000),((8435964341:ℚ)/10000000000),((-7075964341:ℚ)/15250000000),((-1458853327:ℚ)/4320000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((13272675844052086174061735005689125222899491069661063:ℚ)/167961600000000000000000000000000000000000000000000000),((78473977:ℚ)/512000000)⟩
theorem valid12 : Valid source19 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((8374387161:ℚ)/10000000000),((1034054107:ℚ)/1000000000),((-299351369:ℚ)/540000000),((-47100710127:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((21643543664127220795801327497306645111232280265369838418581:ℚ)/230400000000000000000000000000000000000000000000000000000000),((78473977:ℚ)/512000000)⟩
theorem valid13 : Valid source19 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((10278787803:ℚ)/10000000000),((14145905849:ℚ)/10000000000),((-12785905849:ℚ)/20000000000),((-20143838207:ℚ)/73600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((204060854942543522287356994540295998380586992360692713727:ℚ)/1868851200000000000000000000000000000000000000000000000000),((78473977:ℚ)/512000000)⟩
theorem valid14 : Valid source19 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC09
#check @N11Formalization.C450Source19GroupedC09.bound
#print axioms N11Formalization.C450Source19GroupedC09.valid0
#print axioms N11Formalization.C450Source19GroupedC09.valid1
#print axioms N11Formalization.C450Source19GroupedC09.valid2
#print axioms N11Formalization.C450Source19GroupedC09.valid3
#print axioms N11Formalization.C450Source19GroupedC09.valid4
#print axioms N11Formalization.C450Source19GroupedC09.valid5
#print axioms N11Formalization.C450Source19GroupedC09.valid6
#print axioms N11Formalization.C450Source19GroupedC09.valid7
#print axioms N11Formalization.C450Source19GroupedC09.valid8
#print axioms N11Formalization.C450Source19GroupedC09.valid9
#print axioms N11Formalization.C450Source19GroupedC09.valid10
#print axioms N11Formalization.C450Source19GroupedC09.valid11
#print axioms N11Formalization.C450Source19GroupedC09.valid12
#print axioms N11Formalization.C450Source19GroupedC09.valid13
#print axioms N11Formalization.C450Source19GroupedC09.valid14
#print axioms N11Formalization.C450Source19GroupedC09.bound
#print axioms N11Formalization.C450Source19GroupedC09.endpoint_checks
