import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/4),((5:ℚ)/16),((1414845607:ℚ)/2500000000),((1499268151:ℚ)/2500000000),((2694845607:ℚ)/6437500000),((2555268151:ℚ)/4960000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((913472069:ℚ)/1250000000),((-475767758408540226031602198443898979998972424353479079891:ℚ)/1602341685485839843750000000000000000000000000000000000000),((-63234108030096685922460577:ℚ)/184832000000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((5901703233:ℚ)/10000000000),((1559733687:ℚ)/2500000000),((11021703233:ℚ)/26700000000),((2615733687:ℚ)/5150000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((3408204397:ℚ)/5000000000),((-91869708571739638465277442253343488959501882441897392552041:ℚ)/315520992604687500000000000000000000000000000000000000000000),((-190171749446750826107127139:ℚ)/554496000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((95994863:ℚ)/156250000),((6359748431:ℚ)/10000000000),((175994863:ℚ)/424609375),((10583748431:ℚ)/21360000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((6294051917:ℚ)/10000000000),((-6785613218658958184096552629895052659697007239956840980531:ℚ)/23285200079184722900390625000000000000000000000000000000000),((-1027096237519138954084872497:ℚ)/2957312000000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((6264534917:ℚ)/10000000000),((1296097883:ℚ)/2000000000),((1626362131:ℚ)/3950000000),((2140897883:ℚ)/4348000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((376165859:ℚ)/625000000),((-6162364819028874379671342279365805578362296692428712607881:ℚ)/21333969660314941406250000000000000000000000000000000000000),((-41112353522471795419178153:ℚ)/118292480000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((3192662049:ℚ)/5000000000),((3300580753:ℚ)/5000000000),((5752662049:ℚ)/14062500000),((5412580753:ℚ)/11060000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1432979817:ℚ)/2500000000),((-225831356471505388457355094781499776260498709537202060869:ℚ)/788446236401796340942382812500000000000000000000000000000),((-257077536005367305022935793:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((6506042677:ℚ)/10000000000),((3360884123:ℚ)/5000000000),((11626042677:ℚ)/28600000000),((5472884123:ℚ)/11250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1358003921:ℚ)/2500000000),((-1121640129782544117056550892904126457076788210131954123207:ℚ)/3947679450000000000000000000000000000000000000000000000000),((-257150139035175527345557033:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((6626694287:ℚ)/10000000000),((855289117:ℚ)/1250000000),((11746694287:ℚ)/29075000000),((1383289117:ℚ)/2860000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5116589229:ℚ)/10000000000),((-885684571159689329617268001109130683203484309773727444528151:ℚ)/3141313368008105468750000000000000000000000000000000000000000),((-16073131993862896757644153:ℚ)/46208000000000000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((6747282313:ℚ)/10000000000),((3481399329:ℚ)/5000000000),((3955760771:ℚ)/9850000000),((5593399329:ℚ)/11630000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1195632461:ℚ)/2500000000),((-2869435445622960869489930031251881336048607743111941663239:ℚ)/10252314515820312500000000000000000000000000000000000000000),((-771412624529842200415832371:ℚ)/2217984000000000000000000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((1373561983:ℚ)/2000000000),((1800901131:ℚ)/2500000000),((2397561983:ℚ)/6100000000),((952300377:ℚ)/1970000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2212789439:ℚ)/5000000000),((-45174676895309501427556088355551952648325377878035514500693:ℚ)/165166980543750000000000000000000000000000000000000000000000),((-190461094217678011385116891:ℚ)/554496000000000000000000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((888586933:ℚ)/1250000000),((3842311833:ℚ)/5000000000),((1528586933:ℚ)/4050000000),((5954311833:ℚ)/12200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((3615358881:ℚ)/10000000000),((-135071077285119173641861674456886521499027846076945035783:ℚ)/514971864843750000000000000000000000000000000000000000000),((-41001364656515083:ℚ)/121600000000000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((1517971883:ℚ)/2000000000),((2400725701:ℚ)/2500000000),((2541971883:ℚ)/8000000000),((3456725701:ℚ)/6480000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((516639979:ℚ)/10000000000),((-520129891257778885212678363450106571820427860562223907331:ℚ)/2332800000000000000000000000000000000000000000000000000000),((-3616876844269607:ℚ)/10240000000000000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((9508576363:ℚ)/10000000000),((6712117579:ℚ)/5000000000),((4876192121:ℚ)/18400000000),((8824117579:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-5532069022405147559951737885531514233432380689066870731:ℚ)/29200800000000000000000000000000000000000000000000000000),((-362033591:ℚ)/1024000000)⟩
theorem valid11 : Valid source34 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC21
#check @N11Formalization.C450Source34GroupedC21.bound
#print axioms N11Formalization.C450Source34GroupedC21.valid0
#print axioms N11Formalization.C450Source34GroupedC21.valid1
#print axioms N11Formalization.C450Source34GroupedC21.valid2
#print axioms N11Formalization.C450Source34GroupedC21.valid3
#print axioms N11Formalization.C450Source34GroupedC21.valid4
#print axioms N11Formalization.C450Source34GroupedC21.valid5
#print axioms N11Formalization.C450Source34GroupedC21.valid6
#print axioms N11Formalization.C450Source34GroupedC21.valid7
#print axioms N11Formalization.C450Source34GroupedC21.valid8
#print axioms N11Formalization.C450Source34GroupedC21.valid9
#print axioms N11Formalization.C450Source34GroupedC21.valid10
#print axioms N11Formalization.C450Source34GroupedC21.valid11
#print axioms N11Formalization.C450Source34GroupedC21.bound
#print axioms N11Formalization.C450Source34GroupedC21.endpoint_checks
