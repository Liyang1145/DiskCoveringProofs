import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((5498131539:ℚ)/10000000000),((1210798633:ℚ)/2000000000),((19694394617:ℚ)/26700000000),((18428382229:ℚ)/19840000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1905066481:ℚ)/2500000000),((-67318712648694920470741275180864932833:ℚ)/475854075000000000000000000000000000000),((-1645934914489689121496123:ℚ)/4620800000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((2987256843:ℚ)/5000000000),((157305427:ℚ)/250000000),((10561770529:ℚ)/13825000000),((2380970551:ℚ)/2670000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((266515937:ℚ)/400000000),((-4018201789247631763336215805321354881348170409900329741:ℚ)/24772320849609375000000000000000000000000000000000000000),((-70332307623841182073:ℚ)/200000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((1242526649:ℚ)/2000000000),((6530392699:ℚ)/10000000000),((4367579947:ℚ)/5720000000),((98335105087:ℚ)/110600000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((3069116897:ℚ)/5000000000),((-94921213785992543825283373344704241117092847010133701:ℚ)/584841400000000000000000000000000000000000000000000000),((-40093681707858164645649907:ℚ)/115520000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((3225355747:ℚ)/5000000000),((1662365971:ℚ)/2500000000),((11276067241:ℚ)/14537500000),((24970757623:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5571267771:ℚ)/10000000000),((-1235610717923834679192908092438128029626972810103377109:ℚ)/7200795350646972656250000000000000000000000000000000000),((-2489147793910600231513087:ℚ)/7220000000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((3284868199:ℚ)/5000000000),((3384262351:ℚ)/5000000000),((58145201:ℚ)/75000000),((50715410563:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1316907297:ℚ)/2500000000),((-169487519730580500963630970331737131078364931101:ℚ)/988769531250000000000000000000000000000000000000),((-9889397087564892250593107:ℚ)/28880000000000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((1337750487:ℚ)/2000000000),((6887575649:ℚ)/10000000000),((4653251461:ℚ)/6005000000),((102978483437:ℚ)/118200000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((123681411:ℚ)/250000000),((-347615050976584740818939387042587871395442390334344609:ℚ)/2030066719921875000000000000000000000000000000000000000),((-39287351909231173456836107:ℚ)/115520000000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((6807760027:ℚ)/10000000000),((1751654297:ℚ)/2500000000),((23623280081:ℚ)/30500000000),((26131505861:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2303315729:ℚ)/5000000000),((-15166560296498552425228222965560526287706538970602960423:ℚ)/88664453125000000000000000000000000000000000000000000000),((-2438478418036046470881263:ℚ)/7220000000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((6926759571:ℚ)/10000000000),((7125649753:ℚ)/10000000000),((23980278713:ℚ)/30975000000),((106073446789:ℚ)/122000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2120423689:ℚ)/5000000000),((-1322491267918991907568951665347681293560600887330793037:ℚ)/7739318518066406250000000000000000000000000000000000000),((-38742496041032730698206363:ℚ)/115520000000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((7045751437:ℚ)/10000000000),((7244673753:ℚ)/10000000000),((24337254311:ℚ)/31450000000),((35873586263:ℚ)/41300000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((120084197:ℚ)/312500000),((-16205314672334748450268672020981656745934264668997337:ℚ)/94931865310668945312500000000000000000000000000000000),((-38467875355535168614014363:ℚ)/115520000000000000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((895591997:ℚ)/1250000000),((1870674393:ℚ)/2500000000),((3086775991:ℚ)/4050000000),((27678767109:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((3400786981:ℚ)/10000000000),((-1248247858554820467043619689506841076568541587297091:ℚ)/7688671875000000000000000000000000000000000000000000),((-6564100694211420874263:ℚ)/20000000000000000000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((1480536873:ℚ)/2000000000),((9385990189:ℚ)/10000000000),((5081610619:ℚ)/8000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((456733713:ℚ)/2000000000),((-24368179778992044982556194659690469921212772008806399:ℚ)/300000000000000000000000000000000000000000000000000000),((-8341103:ℚ)/25600000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((4652751557:ℚ)/5000000000),((13189851343:ℚ)/10000000000),((15558254671:ℚ)/27600000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-85245488737374370866813804912243331:ℚ)/2628072000000000000000000000000000000),((-8341103:ℚ)/25600000)⟩
theorem valid11 : Valid source22 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC29
#check @N11Formalization.C450Source22GroupedC29.bound
#print axioms N11Formalization.C450Source22GroupedC29.valid0
#print axioms N11Formalization.C450Source22GroupedC29.valid1
#print axioms N11Formalization.C450Source22GroupedC29.valid2
#print axioms N11Formalization.C450Source22GroupedC29.valid3
#print axioms N11Formalization.C450Source22GroupedC29.valid4
#print axioms N11Formalization.C450Source22GroupedC29.valid5
#print axioms N11Formalization.C450Source22GroupedC29.valid6
#print axioms N11Formalization.C450Source22GroupedC29.valid7
#print axioms N11Formalization.C450Source22GroupedC29.valid8
#print axioms N11Formalization.C450Source22GroupedC29.valid9
#print axioms N11Formalization.C450Source22GroupedC29.valid10
#print axioms N11Formalization.C450Source22GroupedC29.valid11
#print axioms N11Formalization.C450Source22GroupedC29.bound
#print axioms N11Formalization.C450Source22GroupedC29.endpoint_checks
