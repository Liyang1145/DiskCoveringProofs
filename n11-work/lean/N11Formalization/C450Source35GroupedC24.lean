import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((7:ℚ)/16),((1:ℚ)/2),((2703550557:ℚ)/5000000000),((287481257:ℚ)/500000000),((29484853899:ℚ)/51500000000),((423481257:ℚ)/620000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((311688687:ℚ)/400000000),((-55843216598799587781442215823583152232416239804410991:ℚ)/153423650000000000000000000000000000000000000000000000),((-237061321588985160709:ℚ)/564062500000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((5648839247:ℚ)/10000000000),((5991117151:ℚ)/10000000000),((60661874729:ℚ)/106800000000),((8711117151:ℚ)/12875000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1465707409:ℚ)/2000000000),((-321740373293240036653585204217058375080068427652987410533:ℚ)/890375088500976562500000000000000000000000000000000000000),((-375940527242367870747439:ℚ)/902500000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((5890268257:ℚ)/10000000000),((1527938991:ℚ)/2500000000),((62351877799:ℚ)/108700000000),((2207938991:ℚ)/3337500000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((6840253771:ℚ)/10000000000),((-10314990371584548848633587559400584175563299110314902097:ℚ)/28062791857910156250000000000000000000000000000000000000),((-47046775417644578412343:ℚ)/112812500000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((6010877299:ℚ)/10000000000),((3116164189:ℚ)/5000000000),((63196141093:ℚ)/110600000000),((4476164189:ℚ)/6793750000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((823137481:ℚ)/1250000000),((-6200265446567112551124343091705163585864904570265475917:ℚ)/16933777884459495544433593750000000000000000000000000000),((-93623843796607616056069:ℚ)/225625000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/16),((1:ℚ)/2),((6131421013:ℚ)/10000000000),((317641893:ℚ)/500000000),((64039947091:ℚ)/112500000000),((453641893:ℚ)/691250000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((395086407:ℚ)/625000000),((-26475154043268092263679388817321494654746322686197:ℚ)/72575158739089965820312500000000000000000000000000),((-1862686346687848267747:ℚ)/4512500000000000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((6251902807:ℚ)/10000000000),((1618321909:ℚ)/2500000000),((64883319649:ℚ)/114400000000),((255369101:ℚ)/390625000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((6047948001:ℚ)/10000000000),((-19364908028677623560643329969421385464379627495122107:ℚ)/53271651268005371093750000000000000000000000000000000),((-46312494892692120419693:ℚ)/112812500000000000000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((1274465171:ℚ)/2000000000),((1318736143:ℚ)/2000000000),((13145256197:ℚ)/23260000000),((1862736143:ℚ)/2860000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5763379493:ℚ)/10000000000),((-5600500657864677815628908608212560065837303489048563551:ℚ)/15458421550000000000000000000000000000000000000000000000),((-14735340514991226959311:ℚ)/36100000000000000000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((1298538623:ℚ)/2000000000),((3357009953:ℚ)/5000000000),((13313770361:ℚ)/23640000000),((4717009953:ℚ)/7268750000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2732951923:ℚ)/5000000000),((-128074690007362321119032927831842552762375364658826120183:ℚ)/354639171019363403320312500000000000000000000000000000000),((-91546998544299842084701:ℚ)/225625000000000000000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((132260147:ℚ)/200000000),((6834307833:ℚ)/10000000000),((1348221029:ℚ)/2402000000),((9554307833:ℚ)/14775000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1288312787:ℚ)/2500000000),((-726418638301062107559689258429064647413977528427804831331:ℚ)/2017549725512695312500000000000000000000000000000000000000),((-363913462547829283340471:ℚ)/902500000000000000000000)⟩
theorem valid8 : Valid source35 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((3366635571:ℚ)/5000000000),((869318369:ℚ)/1250000000),((34126448997:ℚ)/61000000000),((1209318369:ℚ)/1876562500),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4822434153:ℚ)/10000000000),((-904519000376579072532656771664666033512963889783941241:ℚ)/2519410602116584777832031250000000000000000000000000000),((-22597498348325801438791:ℚ)/56406250000000000000000)⟩
theorem valid9 : Valid source35 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source35 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source35 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((3426743453:ℚ)/5000000000),((1487011857:ℚ)/2000000000),((34547204171:ℚ)/64800000000),((2031011857:ℚ)/3050000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((4469383487:ℚ)/10000000000),((-4859818241399742995902788245577025815115068712247529977:ℚ)/14363641406250000000000000000000000000000000000000000000),((-13787704442357518542311:ℚ)/36100000000000000000000)⟩
theorem valid10 : Valid source35 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((7333912899:ℚ)/10000000000),((9351805429:ℚ)/10000000000),((72457390293:ℚ)/160000000000),((4023935143:ℚ)/5400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((663491619:ℚ)/2500000000),((-88854058487047923416588265010818399117116920750868941:ℚ)/328050000000000000000000000000000000000000000000000000),((-233586890808641:ℚ)/608000000000000)⟩
theorem valid11 : Valid source35 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((4625198887:ℚ)/5000000000),((3292839591:ℚ)/2500000000),((42936392209:ℚ)/110400000000),((3972839591:ℚ)/5000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-2933417590885666866427708150513538034949697548831579691:ℚ)/13476562500000000000000000000000000000000000000000000000),((-1246853:ℚ)/3200000)⟩
theorem valid12 : Valid source35 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source35 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source35 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source35 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC24
#check @N11Formalization.C450Source35GroupedC24.bound
#print axioms N11Formalization.C450Source35GroupedC24.valid0
#print axioms N11Formalization.C450Source35GroupedC24.valid1
#print axioms N11Formalization.C450Source35GroupedC24.valid2
#print axioms N11Formalization.C450Source35GroupedC24.valid3
#print axioms N11Formalization.C450Source35GroupedC24.valid4
#print axioms N11Formalization.C450Source35GroupedC24.valid5
#print axioms N11Formalization.C450Source35GroupedC24.valid6
#print axioms N11Formalization.C450Source35GroupedC24.valid7
#print axioms N11Formalization.C450Source35GroupedC24.valid8
#print axioms N11Formalization.C450Source35GroupedC24.valid9
#print axioms N11Formalization.C450Source35GroupedC24.valid10
#print axioms N11Formalization.C450Source35GroupedC24.valid11
#print axioms N11Formalization.C450Source35GroupedC24.valid12
#print axioms N11Formalization.C450Source35GroupedC24.bound
#print axioms N11Formalization.C450Source35GroupedC24.endpoint_checks
