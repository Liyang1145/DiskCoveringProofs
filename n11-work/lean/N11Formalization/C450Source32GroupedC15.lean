import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/8),((-1:ℚ)/16),((6152728903:ℚ)/10000000000),((1619111249:ℚ)/2500000000),((780888751:ℚ)/12875000000),((13687271097:ℚ)/99200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6273777857:ℚ)/10000000000),((-299615634605756613386555102656652770677656826429493769:ℚ)/8003371582031250000000000000000000000000000000000000000),((-3409436663411141335205371:ℚ)/20480000000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((3197460673:ℚ)/5000000000),((6597240813:ℚ)/10000000000),((3002759187:ℚ)/52450000000),((6722539327:ℚ)/51500000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((142714797:ℚ)/250000000),((-1580938108173805294882865433266888932288003412215787991:ℚ)/45090650351562500000000000000000000000000000000000000000),((-329117012694966437676864611:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((3257943233:ℚ)/5000000000),((1343592403:ℚ)/2000000000),((576407597:ℚ)/10680000000),((6662056767:ℚ)/52450000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((1081380937:ℚ)/2000000000),((-12480102043577926112147391908987766063662394785192449:ℚ)/380683260000000000000000000000000000000000000000000000),((-339856341248927579850058851:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((6636770631:ℚ)/10000000000),((1709653161:ℚ)/2500000000),((690346839:ℚ)/13587500000),((13203229369:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((254472249:ℚ)/500000000),((-95981561681908046273864387315012203980214697889676947:ℚ)/3135657966308593750000000000000000000000000000000000000),((-4207407146434730230073083097:ℚ)/22179840000000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((6757578239:ℚ)/10000000000),((275956507:ℚ)/400000000),((108043493:ℚ)/2193000000),((13082421761:ℚ)/108700000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2376504903:ℚ)/5000000000),((-32480751651985851987981349689884114295402169358107:ℚ)/1098612818437500000000000000000000000000000000000000),((-1445600443313682359749434339:ℚ)/7393280000000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((340897731:ℚ)/500000000),((6959196449:ℚ)/10000000000),((2640803551:ℚ)/55300000000),((651102269:ℚ)/5482500000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4576364393:ℚ)/10000000000),((-40397506821923836065318612908547710303810186073680063:ℚ)/1415561191406250000000000000000000000000000000000000000),((-11003995680728242897008497:ℚ)/55449600000000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((859789171:ℚ)/1250000000),((176992923:ℚ)/250000000),((21002359:ℚ)/468750000),((1620210829:ℚ)/13825000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1098299179:ℚ)/2500000000),((-40050327149556095040438247433672195595397523561:ℚ)/1508742570877075195312500000000000000000000000000),((-23262824871316394220179419:ℚ)/115520000000000000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((6998979811:ℚ)/10000000000),((1440035461:ℚ)/2000000000),((479964539:ℚ)/11440000000),((1426780021:ℚ)/12500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2001830117:ℚ)/5000000000),((-46117281617436186243997736692705713217552962310449847:ℚ)/1871492480000000000000000000000000000000000000000000000),((-1532131250634388673154775739:ℚ)/7393280000000000000000000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((71195811:ℚ)/100000000),((7440929727:ℚ)/10000000000),((719690091:ℚ)/19700000000),((127204189:ℚ)/1144000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1787322771:ℚ)/5000000000),((-50304501094634747020141344581531175370301503254408063:ℚ)/2389179062500000000000000000000000000000000000000000000),((-472659869062955191831217:ℚ)/2217984000000000000000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((7360601157:ℚ)/10000000000),((3840737811:ℚ)/5000000000),((959262189:ℚ)/30500000000),((12479398843:ℚ)/118200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1258304903:ℚ)/5000000000),((-629534709484936098319388427875571740862092269884031977:ℚ)/35465781250000000000000000000000000000000000000000000000),((-4987841090666550883628918273:ℚ)/22179840000000000000000000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((3800698671:ℚ)/5000000000),((8162022219:ℚ)/10000000000),((159775309:ℚ)/7200000000),((6119301329:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-1837762476003476054094522663324078810572736225944579:ℚ)/155520000000000000000000000000000000000000000000000000),((-121160777:ℚ)/512000000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((1010299861:ℚ)/1250000000),((10079032701:ℚ)/10000000000),((-159677567:ℚ)/21600000000),((1469700139:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((15828247261495866287935197514631796346686865408688617:ℚ)/2361960000000000000000000000000000000000000000000000000),((-121160777:ℚ)/512000000)⟩
theorem valid11 : Valid source32 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((500031241:ℚ)/500000000),((1390005093:ℚ)/1000000000),((-430005093:ℚ)/8000000000),((491968759:ℚ)/8000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((966350268962464849984319349205443:ℚ)/25600000000000000000000000000000000),((-121160777:ℚ)/512000000)⟩
theorem valid12 : Valid source32 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC15
#check @N11Formalization.C450Source32GroupedC15.bound
#print axioms N11Formalization.C450Source32GroupedC15.valid0
#print axioms N11Formalization.C450Source32GroupedC15.valid1
#print axioms N11Formalization.C450Source32GroupedC15.valid2
#print axioms N11Formalization.C450Source32GroupedC15.valid3
#print axioms N11Formalization.C450Source32GroupedC15.valid4
#print axioms N11Formalization.C450Source32GroupedC15.valid5
#print axioms N11Formalization.C450Source32GroupedC15.valid6
#print axioms N11Formalization.C450Source32GroupedC15.valid7
#print axioms N11Formalization.C450Source32GroupedC15.valid8
#print axioms N11Formalization.C450Source32GroupedC15.valid9
#print axioms N11Formalization.C450Source32GroupedC15.valid10
#print axioms N11Formalization.C450Source32GroupedC15.valid11
#print axioms N11Formalization.C450Source32GroupedC15.valid12
#print axioms N11Formalization.C450Source32GroupedC15.bound
#print axioms N11Formalization.C450Source32GroupedC15.endpoint_checks
