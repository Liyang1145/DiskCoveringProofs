import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((1596854371:ℚ)/2500000000),((6710773929:ℚ)/10000000000),((-2998773929:ℚ)/19840000000),((-396854371:ℚ)/6437500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2863419107:ℚ)/5000000000),((2336162787785598279351030936661067357201:ℚ)/20712830992384000000000000000000000000000),((-468014059505806885865809:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((6628762199:ℚ)/10000000000),((6831395209:ℚ)/10000000000),((-3119395209:ℚ)/20600000000),((-1828762199:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1277757321:ℚ)/2500000000),((26246185460577713474609748170851528986804345938990234587323:ℚ)/234851149126367187500000000000000000000000000000000000000000),((-29982552798890473743609:ℚ)/640000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((1687331919:ℚ)/2500000000),((6891680073:ℚ)/10000000000),((-3179680073:ℚ)/20980000000),((-487331919:ℚ)/6615625000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((477667887:ℚ)/1000000000),((394363155832862392053072405412848357841334244133988304654227:ℚ)/3543360380202850000000000000000000000000000000000000000000000),((-781818372740165927522889:ℚ)/14440000000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((272383417:ℚ)/400000000),((6951948383:ℚ)/10000000000),((-3239948383:ℚ)/21170000000),((-80383417:ℚ)/1068000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((1150306391:ℚ)/2500000000),((13142223157591762381369395598826670185221703901468449995741:ℚ)/117425552797770312500000000000000000000000000000000000000000),((-21369949082112691436161:ℚ)/369664000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/16),((-1:ℚ)/4),((6869827123:ℚ)/10000000000),((701220059:ℚ)/1000000000),((-330020059:ℚ)/2136000000),((-2069827123:ℚ)/26937500000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4419377023:ℚ)/10000000000),((141473110795458569690429588197939356467959824213967273633:ℚ)/1257175165526400000000000000000000000000000000000000000000),((-14206299479625131959252921:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((866256651:ℚ)/1250000000),((7072437129:ℚ)/10000000000),((-3360437129:ℚ)/21550000000),((-266256651:ℚ)/3396875000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((169212127:ℚ)/400000000),((8361421718513386640354875962131480976005525644672713445265747:ℚ)/73906209541311718750000000000000000000000000000000000000000000),((-235302211647361414900149:ℚ)/3610000000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((6990264101:ℚ)/10000000000),((3566329209:ℚ)/5000000000),((-1710329209:ℚ)/10870000000),((-2190264101:ℚ)/27412500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((201649119:ℚ)/500000000),((30489850271049795307729575211872423956029826942864974369003:ℚ)/268091732245540234375000000000000000000000000000000000000000),((-15915347896458670767390249:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((7050460209:ℚ)/10000000000),((7192864863:ℚ)/10000000000),((-3480864863:ℚ)/21930000000),((-2250460209:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3826133173:ℚ)/10000000000),((5954339199301657541365378439700843910481118512335788976967:ℚ)/52087703471868750000000000000000000000000000000000000000000),((-16774321944815899338110769:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((7110641921:ℚ)/10000000000),((7313234761:ℚ)/10000000000),((-3601234761:ℚ)/22120000000),((-2310641921:ℚ)/28125000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((721622241:ℚ)/2000000000),((4341593942958367672269174146137805022224030242700664161:ℚ)/37273748400000000000000000000000000000000000000000000000),((-17636266930854389152096209:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((361548183:ℚ)/500000000),((7433549783:ℚ)/10000000000),((-3721549783:ℚ)/22500000000),((-121548183:ℚ)/1430000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((625815007:ℚ)/2000000000),((704368411459469303069467877779921662536814989001262475167:ℚ)/5990917968750000000000000000000000000000000000000000000000),((-48422705811520241625561:ℚ)/577600000000000000000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((1470246437:ℚ)/2000000000),((7674026051:ℚ)/10000000000),((-3962026051:ℚ)/22880000000),((-510246437:ℚ)/5910000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((256564819:ℚ)/1000000000),((88377797012652781284563406192092342637717841908661810638297:ℚ)/726307516563200000000000000000000000000000000000000000000000),((-844552722766877475463081:ℚ)/9241600000000000000000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((7591620109:ℚ)/10000000000),((247322301:ℚ)/312500000),((-131322301:ℚ)/738750000),((-2791620109:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((469642403:ℚ)/10000000000),((128785024774933138110388474565682235125684720340296607:ℚ)/1041812729479980468750000000000000000000000000000000000),((-24639138599574905300552569:ℚ)/231040000000000000000000000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((3915912521:ℚ)/5000000000),((1678878113:ℚ)/2000000000),((-936478113:ℚ)/4880000000),((-1515912521:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((52058740309983877673506202902114455437765167419620488417:ℚ)/397125957600000000000000000000000000000000000000000000000),((-13719083:ℚ)/128000000)⟩
theorem valid12 : Valid source31 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((8311751677:ℚ)/10000000000),((10309818823:ℚ)/10000000000),((-2199272941:ℚ)/8640000000),((-3511751677:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1541272753337861794028473629026424756692469360386581:ℚ)/9331200000000000000000000000000000000000000000000000),((-13719083:ℚ)/128000000)⟩
theorem valid13 : Valid source31 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((1022672481:ℚ)/1000000000),((7063920309:ℚ)/5000000000),((-5207920309:ℚ)/16000000000),((-180890827:ℚ)/1840000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((115187000059607379331038619374429904741:ℚ)/541696000000000000000000000000000000000),((-13719083:ℚ)/128000000)⟩
theorem valid14 : Valid source31 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source31 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source31 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source31 nn0 nn1 Qcell ((2117:ℚ)/3200) ((2193:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source31 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source31 nn0 nn1 Qcell ((2193:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source31 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC12
#check @N11Formalization.C450Source31GroupedC12.bound
#print axioms N11Formalization.C450Source31GroupedC12.valid0
#print axioms N11Formalization.C450Source31GroupedC12.valid1
#print axioms N11Formalization.C450Source31GroupedC12.valid2
#print axioms N11Formalization.C450Source31GroupedC12.valid3
#print axioms N11Formalization.C450Source31GroupedC12.valid4
#print axioms N11Formalization.C450Source31GroupedC12.valid5
#print axioms N11Formalization.C450Source31GroupedC12.valid6
#print axioms N11Formalization.C450Source31GroupedC12.valid7
#print axioms N11Formalization.C450Source31GroupedC12.valid8
#print axioms N11Formalization.C450Source31GroupedC12.valid9
#print axioms N11Formalization.C450Source31GroupedC12.valid10
#print axioms N11Formalization.C450Source31GroupedC12.valid11
#print axioms N11Formalization.C450Source31GroupedC12.valid12
#print axioms N11Formalization.C450Source31GroupedC12.valid13
#print axioms N11Formalization.C450Source31GroupedC12.valid14
#print axioms N11Formalization.C450Source31GroupedC12.bound
#print axioms N11Formalization.C450Source31GroupedC12.endpoint_checks
