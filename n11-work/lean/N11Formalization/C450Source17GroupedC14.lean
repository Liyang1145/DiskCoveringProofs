import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((6246355197:ℚ)/10000000000),((3263365663:ℚ)/5000000000),((-4990096989:ℚ)/49600000000),((-1126355197:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((378798369:ℚ)/625000000),((2479967166356979930880643977300732090269687273943069139137:ℚ)/39696723046875000000000000000000000000000000000000000000000),((-223118958247954818412110881:ℚ)/5544960000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((6484916631:ℚ)/10000000000),((676533107:ℚ)/1000000000),((-1069599321:ℚ)/10300000000),((-1364916631:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5485557879:ℚ)/10000000000),((757569703065823928663407926595268861934891814115670516529:ℚ)/12253242431250000000000000000000000000000000000000000000000),((-251405845286755467569807849:ℚ)/5544960000000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((6723402061:ℚ)/10000000000),((6884601917:ℚ)/10000000000),((-3684601917:ℚ)/35600000000),((-1603402061:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4850359983:ℚ)/10000000000),((2720358944917801462503669159994432144309753829528861961957:ℚ)/44651769440234375000000000000000000000000000000000000000000),((-93239754231925678246489963:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((3421309393:ℚ)/5000000000),((1400770951:ℚ)/2000000000),((-2282312853:ℚ)/21740000000),((-123044199:ℚ)/3950000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4502356517:ℚ)/10000000000),((198512858185562647544599321387961349827912963929782681:ℚ)/3271077838134765625000000000000000000000000000000000000),((-24490517351262619102574547:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((6961819383:ℚ)/10000000000),((7123090503:ℚ)/10000000000),((-11769271509:ℚ)/110600000000),((-1841819383:ℚ)/56250000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2063654201:ℚ)/5000000000),((217956498611578787893720137458285135652033265200757820029:ℚ)/3604325652122497558593750000000000000000000000000000000000),((-308060115690735434145749801:ℚ)/5544960000000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((7081004677:ℚ)/10000000000),((44891889:ℚ)/62500000),((-24891889:ℚ)/234375000),((-1961004677:ℚ)/56725000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((929250763:ℚ)/2500000000),((85704907840137205196163251492088568603563303153735981:ℚ)/1425980359985351562500000000000000000000000000000000000),((-107413693236743970634416187:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((3570295913:ℚ)/5000000000),((7242310021:ℚ)/10000000000),((-12126930063:ℚ)/113450000000),((-91845083:ℚ)/2600000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3494780629:ℚ)/10000000000),((7478933383704142116418119310267509234954198017235891319:ℚ)/124624825000000000000000000000000000000000000000000000000),((-27444519625303019708495907:ℚ)/462080000000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((3600087717:ℚ)/5000000000),((3650956973:ℚ)/5000000000),((-473297763:ℚ)/4400000000),((-1040087717:ℚ)/28837500000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((814527117:ℚ)/2500000000),((5789018537943663823939717378859899433146318867957813:ℚ)/96604380278348922729492187500000000000000000000000000),((-84107297020247401199052401:ℚ)/1386240000000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((1814938897:ℚ)/2500000000),((736151411:ℚ)/1000000000),((-416151411:ℚ)/3845000000),((-534938897:ℚ)/14537500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3003567607:ℚ)/10000000000),((441830738865966587038150007213459122006260208539437152529:ℚ)/7383215499530029296875000000000000000000000000000000000000),((-7156790571067558099947027:ℚ)/115520000000000000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((7319332373:ℚ)/10000000000),((3740351759:ℚ)/5000000000),((-6421055277:ℚ)/58150000000),((-733110791:ℚ)/19700000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((545230373:ℚ)/2000000000),((416305647618483135455759975428698519203852704590895560549:ℚ)/6946538124218750000000000000000000000000000000000000000000),((-116874841079328974969666587:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((1859619041:ℚ)/2500000000),((385952053:ℚ)/500000000),((-225952053:ℚ)/1970000000),((-579619041:ℚ)/15250000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((206537399:ℚ)/1000000000),((131233459219531774355065638477734714326658174335919664141:ℚ)/2183362158203125000000000000000000000000000000000000000000),((-7600565874745497382393843:ℚ)/115520000000000000000000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((307069071:ℚ)/400000000),((4097784047:ℚ)/5000000000),((-7493352141:ℚ)/61000000000),((-102269071:ℚ)/2592000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((66904717163892372441241135890255450579092662457990041:ℚ)/1106531020800000000000000000000000000000000000000000000),((-110831:ℚ)/1600000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((8153095379:ℚ)/10000000000),((10100220441:ℚ)/10000000000),((-6900220441:ℚ)/43200000000),((-3033095379:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((101424484736449935359654461717931252984058529366717604267:ℚ)/1600000000000000000000000000000000000000000000000000000000),((-110831:ℚ)/1600000)⟩
theorem valid12 : Valid source17 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((5028632761:ℚ)/5000000000),((6952836863:ℚ)/5000000000),((-16058510589:ℚ)/80000000000),((-822877587:ℚ)/18400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((342050546707759167955874816978012934990829191210703379:ℚ)/4866800000000000000000000000000000000000000000000000000),((-110831:ℚ)/1600000)⟩
theorem valid13 : Valid source17 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source17 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source17 nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC14
#check @N11Formalization.C450Source17GroupedC14.bound
#print axioms N11Formalization.C450Source17GroupedC14.valid0
#print axioms N11Formalization.C450Source17GroupedC14.valid1
#print axioms N11Formalization.C450Source17GroupedC14.valid2
#print axioms N11Formalization.C450Source17GroupedC14.valid3
#print axioms N11Formalization.C450Source17GroupedC14.valid4
#print axioms N11Formalization.C450Source17GroupedC14.valid5
#print axioms N11Formalization.C450Source17GroupedC14.valid6
#print axioms N11Formalization.C450Source17GroupedC14.valid7
#print axioms N11Formalization.C450Source17GroupedC14.valid8
#print axioms N11Formalization.C450Source17GroupedC14.valid9
#print axioms N11Formalization.C450Source17GroupedC14.valid10
#print axioms N11Formalization.C450Source17GroupedC14.valid11
#print axioms N11Formalization.C450Source17GroupedC14.valid12
#print axioms N11Formalization.C450Source17GroupedC14.valid13
#print axioms N11Formalization.C450Source17GroupedC14.bound
#print axioms N11Formalization.C450Source17GroupedC14.endpoint_checks
