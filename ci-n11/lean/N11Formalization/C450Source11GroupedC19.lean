import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((1528134469:ℚ)/2500000000),((1655109243:ℚ)/2500000000),((2248134469:ℚ)/13350000000),((6565327729:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6363312777:ℚ)/10000000000),((6255442876233323666318594844239824185517:ℚ)/271842636672000000000000000000000000000000),((-5022904879848941581910849:ℚ)/57760000000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((6588426293:ℚ)/10000000000),((6858265987:ℚ)/10000000000),((9468426293:ℚ)/55300000000),((26974797961:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1304626357:ℚ)/2500000000),((150815735304157147972551701446182139402786128197036687014661837:ℚ)/6984982023440400000000000000000000000000000000000000000000000000),((-84100910828684564373865441:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((6826324599:ℚ)/10000000000),((3488586071:ℚ)/5000000000),((1078480511:ℚ)/6250000000),((13665758213:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4551374741:ℚ)/10000000000),((3172219528040018980734470645202755139940681889741451349:ℚ)/150993193750000000000000000000000000000000000000000000000),((-257912407311094040316725227:ℚ)/2772480000000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((1:ℚ)/8),((3:ℚ)/16),((6945263637:ℚ)/10000000000),((1407324651:ℚ)/2000000000),((9825263637:ℚ)/56725000000),((5501973953:ℚ)/22500000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((261330291:ℚ)/625000000),((7603539725709231894989009319357369936913139383026667297678103:ℚ)/366519059472656250000000000000000000000000000000000000000000000),((-260719282241778349503048163:ℚ)/2772480000000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((875591347:ℚ)/1250000000),((7096073101:ℚ)/10000000000),((1235591347:ℚ)/7150000000),((27688219303:ℚ)/113450000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1992100297:ℚ)/5000000000),((154377359217181832428880744225615277725437764224921678960137:ℚ)/7464927329623156250000000000000000000000000000000000000000000),((-1365225169198145753410481:ℚ)/14440000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/8),((3:ℚ)/16),((7064196381:ℚ)/10000000000),((447220107:ℚ)/625000000),((3314732127:ℚ)/19225000000),((1741660321:ℚ)/7150000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((75548553:ℚ)/200000000),((20891528420601567135296958839374662821576390161225241724533:ℚ)/1013239438902539062500000000000000000000000000000000000000000),((-263527525786348234352252947:ℚ)/2772480000000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((712366049:ℚ)/1000000000),((3607484559:ℚ)/5000000000),((1000366049:ℚ)/5815000000),((14022453677:ℚ)/57675000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((889818369:ℚ)/2500000000),((444589611986836515720821475059386045803593609280909344981689:ℚ)/21624246980104253906250000000000000000000000000000000000000000),((-883107210036939198664809:ℚ)/9241600000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/8),((3:ℚ)/16),((7183123141:ℚ)/10000000000),((7274415349:ℚ)/10000000000),((10063123141:ℚ)/58625000000),((28223246047:ℚ)/116300000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3327495943:ℚ)/10000000000),((33255499502004856987990262206971887644381970422404184866187811:ℚ)/1621907605630626562500000000000000000000000000000000000000000000),((-88779048343201791305760129:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((452661523:ℚ)/625000000),((7333860433:ℚ)/10000000000),((632661523:ℚ)/3693750000),((4057368757:ℚ)/16750000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((769753839:ℚ)/2500000000),((52450965698675636297100367279556141632364502136017869778307:ℚ)/2564716831127929687500000000000000000000000000000000000000000),((-348623011220963305950561:ℚ)/3610000000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/8),((3:ℚ)/16),((3651022103:ℚ)/5000000000),((7393304397:ℚ)/10000000000),((5091022103:ℚ)/29787500000),((28579913191:ℚ)/118200000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((280939817:ℚ)/1000000000),((3587145815344591921167870522485613166798596077190273798697138667:ℚ)/175833567001787850000000000000000000000000000000000000000000000000),((-22429012214638145962164281:ℚ)/231040000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((230046959:ℚ)/312500000),((1863186817:ℚ)/2500000000),((320046959:ℚ)/1876562500),((7189560451:ℚ)/29787500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2511841677:ℚ)/10000000000),((303098619651349428516618056726838030396268774826109463148901:ℚ)/14891834997348546600341796875000000000000000000000000000000000),((-88071018117631735521329:ℚ)/902500000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((7420959847:ℚ)/10000000000),((1514325967:ℚ)/2000000000),((10300959847:ℚ)/61000000000),((5822977901:ℚ)/24020000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((135931383:ℚ)/625000000),((6581018545884570225255112168497321326797714695084815267331:ℚ)/322298805966050000000000000000000000000000000000000000000000),((-90653512205849515082611481:ℚ)/924160000000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((3769935159:ℚ)/5000000000),((8047121171:ℚ)/10000000000),((1736645053:ℚ)/10800000000),((30541363513:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1258749787:ℚ)/10000000000),((43336632781847005984180442985057185132686723674156853990103:ℚ)/2068364362500000000000000000000000000000000000000000000000000),((-68693580239944001730654187:ℚ)/693120000000000000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((1001933133:ℚ)/1250000000),((9948619217:ℚ)/10000000000),((1361933133:ℚ)/10000000000),((36245857651:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((57572018293245599972404477292834906909227196956855097807:ℚ)/2550916800000000000000000000000000000000000000000000000000),((-1593939:ℚ)/16000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((4958639133:ℚ)/5000000000),((6875188473:ℚ)/5000000000),((2132879711:ℚ)/18400000000),((23825565419:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1820975390267460521257085429407997988047:ℚ)/67712000000000000000000000000000000000000),((-1593939:ℚ)/16000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC19
#check @N11Formalization.C450Source11GroupedC19.bound
#print axioms N11Formalization.C450Source11GroupedC19.valid0
#print axioms N11Formalization.C450Source11GroupedC19.valid1
#print axioms N11Formalization.C450Source11GroupedC19.valid2
#print axioms N11Formalization.C450Source11GroupedC19.valid3
#print axioms N11Formalization.C450Source11GroupedC19.valid4
#print axioms N11Formalization.C450Source11GroupedC19.valid5
#print axioms N11Formalization.C450Source11GroupedC19.valid6
#print axioms N11Formalization.C450Source11GroupedC19.valid7
#print axioms N11Formalization.C450Source11GroupedC19.valid8
#print axioms N11Formalization.C450Source11GroupedC19.valid9
#print axioms N11Formalization.C450Source11GroupedC19.valid10
#print axioms N11Formalization.C450Source11GroupedC19.valid11
#print axioms N11Formalization.C450Source11GroupedC19.valid12
#print axioms N11Formalization.C450Source11GroupedC19.valid13
#print axioms N11Formalization.C450Source11GroupedC19.valid14
#print axioms N11Formalization.C450Source11GroupedC19.bound
#print axioms N11Formalization.C450Source11GroupedC19.endpoint_checks
