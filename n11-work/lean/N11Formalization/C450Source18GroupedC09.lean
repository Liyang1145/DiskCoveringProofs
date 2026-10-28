import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((3226616269:ℚ)/5000000000),((675050749:ℚ)/1000000000),((-547050749:ℚ)/1240000000),((-17146313883:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((556499101:ℚ)/1000000000),((925264235891748220664128614201699605833877999766451909551:ℚ)/13232241015625000000000000000000000000000000000000000000000),((31675605116937864447954489:ℚ)/184832000000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((3345862061:ℚ)/5000000000),((3434874197:ℚ)/5000000000),((-2794874197:ℚ)/6437500000),((-17981034427:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2469507343:ℚ)/5000000000),((786930325960523662767409360944177769855005362634231610463:ℚ)/11610842465527343750000000000000000000000000000000000000000),((31004814392324590479803129:ℚ)/184832000000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((6810942813:ℚ)/10000000000),((436810733:ℚ)/625000000),((-356810733:ℚ)/819531250),((-36796599691:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4597201849:ℚ)/10000000000),((67605646089072101717810323685457145005910767652145970380617:ℚ)/998341849350000000000000000000000000000000000000000000000000),((122671535073516854012382681:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((6930144733:ℚ)/10000000000),((3524288549:ℚ)/5000000000),((-2884288549:ℚ)/6675000000),((-37631013131:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((846001963:ℚ)/2000000000),((90705080919613044124346687828942558892749887337242282777:ℚ)/1359101524162292480468750000000000000000000000000000000000),((121319706426753500211526361:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((6989739683:ℚ)/10000000000),((3554089209:ℚ)/5000000000),((-2914089209:ℚ)/6734375000),((-38048177781:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2017370123:ℚ)/5000000000),((115426038151857608703424820107419370531583163375033618329433:ℚ)/1729879786853125000000000000000000000000000000000000000000000),((120642249687814873660147161:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7049330767:ℚ)/10000000000),((3583887897:ℚ)/5000000000),((-2943887897:ℚ)/6793750000),((-38465315369:ℚ)/109650000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3830111717:ℚ)/10000000000),((24895523469149708175269039593511209824971092331544389879143:ℚ)/373185041762988281250000000000000000000000000000000000000000),((119963763357718533934309361:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((3554459043:ℚ)/5000000000),((722736933:ℚ)/1000000000),((-594736933:ℚ)/1370625000),((-19441213301:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3614530647:ℚ)/10000000000),((15288472763086792175633280192684295012052517812256323329:ℚ)/229222361279296875000000000000000000000000000000000000000),((29821061623177926070947801:ℚ)/184832000000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((358425087:ℚ)/500000000),((7286959123:ℚ)/10000000000),((-6006959123:ℚ)/13825000000),((-1964975609:ℚ)/5577500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1692950481:ℚ)/5000000000),((178522884961571482667184715935531938293126287078252037:ℚ)/2677169491238403320312500000000000000000000000000000000),((296509245382954636488081:ℚ)/1848320000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/2),((-7:ℚ)/16),((361404091:ℚ)/500000000),((1836636317:ℚ)/2500000000),((-1516636317:ℚ)/3485937500),((-661942879:ℚ)/1875000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((785342493:ℚ)/2500000000),((35905779710944880800721568260535658626666374804011801:ℚ)/538560748100280761718750000000000000000000000000000000),((294805293738344651590569:ℚ)/1848320000000000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((364382921:ℚ)/500000000),((7406127859:ℚ)/10000000000),((-6126127859:ℚ)/14062500000),((-2006680447:ℚ)/5672500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((575376083:ℚ)/2000000000),((855456621588500702179508857463213471684449709235949:ℚ)/12833823239868164062500000000000000000000000000000000),((293098759086051193280609:ℚ)/1848320000000000000000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((3673615813:ℚ)/5000000000),((1493141397:ℚ)/2000000000),((-1237141397:ℚ)/2836250000),((-20275310691:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2586310483:ℚ)/10000000000),((88435649897008087564745693880044036371804940465004537053477:ℚ)/1327005136600000000000000000000000000000000000000000000000000),((29138963942691397992384681:ℚ)/184832000000000000000000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((1851700381:ℚ)/2500000000),((7584855181:ℚ)/10000000000),((-6304855181:ℚ)/14300000000),((-10241902667:ℚ)/29075000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2259614639:ℚ)/10000000000),((740951031318850351362271611278935755174479751135597811103:ℚ)/10983613174853515625000000000000000000000000000000000000000),((7241948318656458513369689:ℚ)/46208000000000000000000000)⟩
theorem valid11 : Valid source18 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((3762965861:ℚ)/5000000000),((3851995257:ℚ)/5000000000),((-3211995257:ℚ)/7268750000),((-20900761027:ℚ)/59100000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((174657679:ℚ)/1250000000),((468283496881532758404236935002478559809804860071135644001:ℚ)/6946538124218750000000000000000000000000000000000000000000),((28624675070337956978359529:ℚ)/184832000000000000000000000)⟩
theorem valid12 : Valid source18 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/2),((-7:ℚ)/16),((7645049641:ℚ)/10000000000),((3971112503:ℚ)/5000000000),((-3331112503:ℚ)/7387500000),((-42635347487:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((231116621789234778737628382641340172035172885107998035404339:ℚ)/3353644275000000000000000000000000000000000000000000000000000),((39350143:ℚ)/256000000)⟩
theorem valid13 : Valid source18 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((7883250947:ℚ)/10000000000),((8418564231:ℚ)/10000000000),((-7138564231:ℚ)/15250000000),((-14767585543:ℚ)/43200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((366820668654228588571885203857912119624751940612537177467:ℚ)/5122828800000000000000000000000000000000000000000000000000),((39350143:ℚ)/256000000)⟩
theorem valid14 : Valid source18 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((8359529687:ℚ)/10000000000),((10322644943:ℚ)/10000000000),((-1004738327:ℚ)/1800000000),((-47636707809:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((9787662066995013598656305693401250679027834628367860882883:ℚ)/115200000000000000000000000000000000000000000000000000000000),((39350143:ℚ)/256000000)⟩
theorem valid15 : Valid source18 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((10263426263:ℚ)/10000000000),((14127429059:ℚ)/10000000000),((-12847429059:ℚ)/20000000000),((-20321327947:ℚ)/73600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((92140890916599815758528351115055984031571477953441070267:ℚ)/934425600000000000000000000000000000000000000000000000000),((39350143:ℚ)/256000000)⟩
theorem valid16 : Valid source18 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source18 nn0 nn1 Qcell ((1049:ℚ)/1600) ((431:ℚ)/640) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source18 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source18 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source18 nn0 nn1 Qcell ((431:ℚ)/640) ((2231:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source18 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source18 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source18 nn0 nn1 Qcell ((2231:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source18 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC09
#check @N11Formalization.C450Source18GroupedC09.bound
#print axioms N11Formalization.C450Source18GroupedC09.valid0
#print axioms N11Formalization.C450Source18GroupedC09.valid1
#print axioms N11Formalization.C450Source18GroupedC09.valid2
#print axioms N11Formalization.C450Source18GroupedC09.valid3
#print axioms N11Formalization.C450Source18GroupedC09.valid4
#print axioms N11Formalization.C450Source18GroupedC09.valid5
#print axioms N11Formalization.C450Source18GroupedC09.valid6
#print axioms N11Formalization.C450Source18GroupedC09.valid7
#print axioms N11Formalization.C450Source18GroupedC09.valid8
#print axioms N11Formalization.C450Source18GroupedC09.valid9
#print axioms N11Formalization.C450Source18GroupedC09.valid10
#print axioms N11Formalization.C450Source18GroupedC09.valid11
#print axioms N11Formalization.C450Source18GroupedC09.valid12
#print axioms N11Formalization.C450Source18GroupedC09.valid13
#print axioms N11Formalization.C450Source18GroupedC09.valid14
#print axioms N11Formalization.C450Source18GroupedC09.valid15
#print axioms N11Formalization.C450Source18GroupedC09.valid16
#print axioms N11Formalization.C450Source18GroupedC09.bound
#print axioms N11Formalization.C450Source18GroupedC09.endpoint_checks
