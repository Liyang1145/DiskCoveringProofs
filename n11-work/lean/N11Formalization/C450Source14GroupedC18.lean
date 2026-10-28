import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((6113496983:ℚ)/10000000000),((6627786797:ℚ)/10000000000),((13793496983:ℚ)/106800000000),((10787786797:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((636118881:ℚ)/1000000000),((26374493065891291310624437048172505288397:ℚ)/724913697792000000000000000000000000000000),((-202787380721404228872004347:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((823753991:ℚ)/1250000000),((343293983:ℚ)/500000000),((1783753991:ℚ)/13825000000),((183764661:ℚ)/890000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((521426567:ℚ)/1000000000),((46631379499324586391796951825830573665274296326240053981:ℚ)/1347411655756250000000000000000000000000000000000000000000),((-537811775695019193465987:ℚ)/4620800000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((1365643989:ℚ)/2000000000),((6984911019:ℚ)/10000000000),((967214663:ℚ)/7500000000),((11144911019:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4545698207:ℚ)/10000000000),((15354970591855597317533851217489879348162996387975759351:ℚ)/452979581250000000000000000000000000000000000000000000000),((-221290893123163045668713963:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((1:ℚ)/16),((1:ℚ)/8),((1736824113:ℚ)/2500000000),((7044423151:ℚ)/10000000000),((3656824113:ℚ)/28362500000),((3734807717:ℚ)/18750000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((4174692521:ℚ)/10000000000),((7122608176886378805557456040940859879660852039542959543903773:ℚ)/212105937194824218750000000000000000000000000000000000000000000),((-224373425381807257327800483:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((7006830587:ℚ)/10000000000),((7103932999:ℚ)/10000000000),((102705109:ℚ)/800000000),((11263932999:ℚ)/56725000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3977072973:ℚ)/10000000000),((1528244769584857958507747339299742621845669828007280159:ℚ)/45631371519531250000000000000000000000000000000000000000),((-225910374756108812394112083:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/16),((1:ℚ)/8),((7066362069:ℚ)/10000000000),((3581720309:ℚ)/5000000000),((4915454023:ℚ)/38450000000),((5661720309:ℚ)/28600000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((942423487:ℚ)/2500000000),((722100521619732515593613959299410748369562443797710945284381:ℚ)/21615774696587500000000000000000000000000000000000000000000000),((-56861796335971462598794923:ℚ)/462080000000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((1781472741:ℚ)/2500000000),((7222946063:ℚ)/10000000000),((3701472741:ℚ)/29075000000),((11382946063:ℚ)/57675000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((443855201:ℚ)/1250000000),((720640035765526077192383545944638195690772712487522964516989:ℚ)/21624246980104253906250000000000000000000000000000000000000000),((-228983858858282100397907427:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/16),((1:ℚ)/8),((1437083467:ℚ)/2000000000),((1820612347:ℚ)/2500000000),((2973083467:ℚ)/23450000000),((2860612347:ℚ)/14537500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1659121019:ℚ)/5000000000),((35108698308212042392224587045812971458581701103114376789643:ℚ)/1055929430749105834960937500000000000000000000000000000000000),((-14407524808403514070327947:ℚ)/115520000000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((7244941243:ℚ)/10000000000),((7341950643:ℚ)/10000000000),((14924941243:ℚ)/118200000000),((11501950643:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((122750641:ℚ)/400000000),((18150162557283610095986651621892574000529678511457153176427:ℚ)/547075791714477539062500000000000000000000000000000000000000),((-232056801155981129058926267:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((7304462749:ℚ)/10000000000),((7460947143:ℚ)/10000000000),((14984462749:ℚ)/120100000000),((11620947143:ℚ)/59100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2797897547:ℚ)/10000000000),((185460976892687576124355574673218332466977562484486160457004589:ℚ)/5582769915665081250000000000000000000000000000000000000000000000),((-233584303781026341284093267:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((7423498783:ℚ)/10000000000),((3789967971:ℚ)/5000000000),((15103498783:ℚ)/122000000000),((5869967971:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2159365483:ℚ)/10000000000),((20831014880563819199511068309837878374043105678854965007099:ℚ)/629489855402441406250000000000000000000000000000000000000000),((-59164079234465117917707803:ℚ)/462080000000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((7542525877:ℚ)/10000000000),((4027910463:ℚ)/5000000000),((15222525877:ℚ)/129600000000),((6107910463:ℚ)/30500000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((246120873:ℚ)/2000000000),((3256659901516384157681367499087000200154556888711547520501:ℚ)/96954579492187500000000000000000000000000000000000000000000),((-7886277172136541:ℚ)/60800000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((1002319093:ℚ)/1250000000),((9958518411:ℚ)/10000000000),((1962319093:ℚ)/20000000000),((14118518411:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((11197561136875126207243268533104333415477071939881313313:ℚ)/318864600000000000000000000000000000000000000000000000000),((-16706001:ℚ)/128000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((496084119:ℚ)/500000000),((6880841139:ℚ)/5000000000),((293361373:ℚ)/3680000000),((8960841139:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((343934815077188075881870122665791425553:ℚ)/8464000000000000000000000000000000000000),((-16706001:ℚ)/128000000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source14 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC18
#check @N11Formalization.C450Source14GroupedC18.bound
#print axioms N11Formalization.C450Source14GroupedC18.valid0
#print axioms N11Formalization.C450Source14GroupedC18.valid1
#print axioms N11Formalization.C450Source14GroupedC18.valid2
#print axioms N11Formalization.C450Source14GroupedC18.valid3
#print axioms N11Formalization.C450Source14GroupedC18.valid4
#print axioms N11Formalization.C450Source14GroupedC18.valid5
#print axioms N11Formalization.C450Source14GroupedC18.valid6
#print axioms N11Formalization.C450Source14GroupedC18.valid7
#print axioms N11Formalization.C450Source14GroupedC18.valid8
#print axioms N11Formalization.C450Source14GroupedC18.valid9
#print axioms N11Formalization.C450Source14GroupedC18.valid10
#print axioms N11Formalization.C450Source14GroupedC18.valid11
#print axioms N11Formalization.C450Source14GroupedC18.valid12
#print axioms N11Formalization.C450Source14GroupedC18.valid13
#print axioms N11Formalization.C450Source14GroupedC18.bound
#print axioms N11Formalization.C450Source14GroupedC18.endpoint_checks
