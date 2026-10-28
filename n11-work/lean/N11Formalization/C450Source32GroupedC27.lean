import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((5:ℚ)/8),((11:ℚ)/16),((2640880427:ℚ)/5000000000),((5618980003:ℚ)/10000000000),((3600880427:ℚ)/5150000000),((81648780033:ℚ)/99200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((8024201891:ℚ)/10000000000),((-4345916723544004096261595851312700624232517222771605709936509:ℚ)/12945519370240000000000000000000000000000000000000000000000000),((-85841060911008837856972557:ℚ)/184832000000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((5521710733:ℚ)/10000000000),((732367851:ℚ)/1250000000),((7441710733:ℚ)/10680000000),((10536046361:ℚ)/12875000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7575220657:ℚ)/10000000000),((-5319119839355917385831092803580049967020894559351949391839:ℚ)/15848676575317382812500000000000000000000000000000000000000),((-3967412605383267018820819:ℚ)/8664000000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((5761483763:ℚ)/10000000000),((5978858677:ℚ)/10000000000),((7681483763:ℚ)/10870000000),((28535815149:ℚ)/35600000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((710417041:ℚ)/1000000000),((-22994440798331447157786840194485586927140430071810295545104153:ℚ)/66637561308880000000000000000000000000000000000000000000000000),((-84068012368361216607537917:ℚ)/184832000000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((735163733:ℚ)/1250000000),((3049366959:ℚ)/5000000000),((975163733:ℚ)/1382500000),((43463036549:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((6858885799:ℚ)/10000000000),((-991642334736983476966650124270999856753270700728239407903931:ℚ)/2876737281056594238281250000000000000000000000000000000000000),((-62574733707880748881023439:ℚ)/138624000000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/8),((11:ℚ)/16),((1200219701:ℚ)/2000000000),((1554642657:ℚ)/2500000000),((1584219701:ℚ)/2250000000),((22061069227:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6606097703:ℚ)/10000000000),((-137099471119929622148622601581122228658457811242357339:ℚ)/398126585083007812500000000000000000000000000000000000),((-15522098978908880734420831:ℚ)/34656000000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((6120851617:ℚ)/10000000000),((158459269:ℚ)/250000000),((8040851617:ℚ)/11440000000),((248783551:ℚ)/312500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3172440719:ℚ)/5000000000),((-268359448722484611627978812960764460897830738909322087:ℚ)/780067443847656250000000000000000000000000000000000000),((-51326664641198337845953:ℚ)/115520000000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((6240571:ℚ)/10000000),((1279651537:ℚ)/2000000000),((8160571:ℚ)/11535000),((1388012839:ℚ)/1760000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1518530391:ℚ)/2500000000),((-164369971684531626296857575900471474370205942509968089:ℚ)/472260894600000000000000000000000000000000000000000000),((-3272496221221998420960837:ℚ)/7393280000000000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((6300418573:ℚ)/10000000000),((6458136139:ℚ)/10000000000),((8220418573:ℚ)/11630000000),((30293165843:ℚ)/38450000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2967373817:ℚ)/5000000000),((-33429410186166160303320027598128013809840515237209483873275591:ℚ)/96107764356018906250000000000000000000000000000000000000000000),((-81473087481535106024865533:ℚ)/184832000000000000000000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((6360258333:ℚ)/10000000000),((1644467117:ℚ)/2500000000),((2760086111:ℚ)/3940000000),((23049138287:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2896225669:ℚ)/5000000000),((-102353680893413496658250124326337107448339547773566575740531:ℚ)/298086044547475585937500000000000000000000000000000000000000),((-5047418775893251082563197:ℚ)/11552000000000000000000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((3239957593:ℚ)/5000000000),((3348784671:ℚ)/5000000000),((4199957593:ℚ)/6005000000),((46756631381:ℚ)/59100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((5498165033:ℚ)/10000000000),((-95761455746143731011541602397155451830496174841333621142028139:ℚ)/279138495783254062500000000000000000000000000000000000000000000),((-60042454203764306089164079:ℚ)/138624000000000000000000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((6599543027:ℚ)/10000000000),((1704310063:ℚ)/2500000000),((8519543027:ℚ)/12200000000),((23707410693:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((518908667:ℚ)/1000000000),((-43153284463948826691061441412598894753662900032889600759001:ℚ)/125897971080488281250000000000000000000000000000000000000000),((-4958819014395814546187637:ℚ)/11552000000000000000000000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((6719143231:ℚ)/10000000000),((7056497697:ℚ)/10000000000),((8639143231:ℚ)/12580000000),((97461474667:ℚ)/122000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1215591319:ℚ)/2500000000),((-225382103315800044366856457987620819886070763478178976345244933:ℚ)/673522423657500000000000000000000000000000000000000000000000000),((-233455617082637490971469871:ℚ)/554496000000000000000000000)⟩
theorem valid11 : Valid source32 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((1391653161:ℚ)/2000000000),((3647825501:ℚ)/5000000000),((591884387:ℚ)/864000000),((50046080511:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2069474957:ℚ)/5000000000),((-683263998554870596471835102054268648037470545054871939277:ℚ)/2042991213750000000000000000000000000000000000000000000000),((-19073433851238056657732173:ℚ)/46208000000000000000000000)⟩
theorem valid12 : Valid source32 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source32 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((1799323077:ℚ)/2500000000),((9206028327:ℚ)/10000000000),((2279323077:ℚ)/4000000000),((121106311597:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((3269939859:ℚ)/10000000000),((-119496282126290581922102088491603780492375107353792130307:ℚ)/510183360000000000000000000000000000000000000000000000000),((-48846570118117699:ℚ)/121600000000000000)⟩
theorem valid13 : Valid source32 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((2276718823:ℚ)/2500000000),((1627271227:ℚ)/1250000000),((2756718823:ℚ)/5520000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-810079648800202931438131:ℚ)/5078400000000000000000000),((-12884301:ℚ)/32000000)⟩
theorem valid14 : Valid source32 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source32 nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2307:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source32 nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source32 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source32 nn0 nn1 Qcell ((2307:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source32 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source32 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC27
#check @N11Formalization.C450Source32GroupedC27.bound
#print axioms N11Formalization.C450Source32GroupedC27.valid0
#print axioms N11Formalization.C450Source32GroupedC27.valid1
#print axioms N11Formalization.C450Source32GroupedC27.valid2
#print axioms N11Formalization.C450Source32GroupedC27.valid3
#print axioms N11Formalization.C450Source32GroupedC27.valid4
#print axioms N11Formalization.C450Source32GroupedC27.valid5
#print axioms N11Formalization.C450Source32GroupedC27.valid6
#print axioms N11Formalization.C450Source32GroupedC27.valid7
#print axioms N11Formalization.C450Source32GroupedC27.valid8
#print axioms N11Formalization.C450Source32GroupedC27.valid9
#print axioms N11Formalization.C450Source32GroupedC27.valid10
#print axioms N11Formalization.C450Source32GroupedC27.valid11
#print axioms N11Formalization.C450Source32GroupedC27.valid12
#print axioms N11Formalization.C450Source32GroupedC27.valid13
#print axioms N11Formalization.C450Source32GroupedC27.valid14
#print axioms N11Formalization.C450Source32GroupedC27.bound
#print axioms N11Formalization.C450Source32GroupedC27.endpoint_checks
