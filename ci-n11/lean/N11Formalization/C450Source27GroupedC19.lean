import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/8),((3:ℚ)/16),((1480065411:ℚ)/2500000000),((6235584193:ℚ)/10000000000),((3480065411:ℚ)/12875000000),((35346752579:ℚ)/99200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6777559621:ℚ)/10000000000),((186726288070584021530714964389076270108809:ℚ)/2589103874048000000000000000000000000000000),((-5355753379261840558504376027:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((770116103:ℚ)/1250000000),((323792611:ℚ)/500000000),((590038701:ℚ)/2225000000),((1803377833:ℚ)/5150000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((3127687357:ℚ)/5000000000),((1862428945832471323360392609319402633829725930752688241:ℚ)/26414460958862304687500000000000000000000000000000000000),((-13743231227191601868260083:ℚ)/36966400000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((3200683211:ℚ)/5000000000),((1319182489:ℚ)/2000000000),((7200683211:ℚ)/27175000000),((7285547467:ℚ)/21360000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5692878597:ℚ)/10000000000),((1594652369782449959274561307309013313415210561786316471356633:ℚ)/23989522071196800000000000000000000000000000000000000000000000),((-226237942635061043068189483:ℚ)/591462400000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((407594177:ℚ)/625000000),((1678981733:ℚ)/2500000000),((129656311:ℚ)/493750000),((9196945199:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1078504043:ℚ)/2000000000),((3231738943597367652913992181298424681571642247632688365647:ℚ)/48924103419329833984375000000000000000000000000000000000000),((-357859671848370553041190947:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((3320799329:ℚ)/5000000000),((1367179609:ℚ)/2000000000),((2440266443:ℚ)/9375000000),((7429538827:ℚ)/22120000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2538196033:ℚ)/5000000000),((5715096749817603293325023150487054992296833395071943533:ℚ)/86972079600000000000000000000000000000000000000000000000),((-231807868312014292685569963:ℚ)/591462400000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((52825347:ℚ)/78125000),((6955827991:ℚ)/10000000000),((115325347:ℚ)/446875000),((37507483973:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2370652353:ℚ)/5000000000),((1323064501698315861218098323459892088104906547024852921999221:ℚ)/20219348144531250000000000000000000000000000000000000000000000),((-5864276298008891034415383563:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((6881646449:ℚ)/10000000000),((283028753:ℚ)/400000000),((14881646449:ℚ)/58150000000),((1514686259:ℚ)/4576000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2191437049:ℚ)/5000000000),((13208094286388252080095746870874753005009315788630612840347:ℚ)/202505816974489600000000000000000000000000000000000000000000),((-9492792400987552668024507:ℚ)/23658496000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((1400321389:ℚ)/2000000000),((719557247:ℚ)/1000000000),((3000321389:ℚ)/11820000000),((3822671741:ℚ)/11630000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((998695471:ℚ)/2500000000),((6206990179659027554234152465743991690791871274771398578277:ℚ)/95387534255192187500000000000000000000000000000000000000000),((-60013551810436957766556507:ℚ)/147865600000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((1780381987:ℚ)/2500000000),((1487035053:ℚ)/2000000000),((3780381987:ℚ)/15250000000),((7789105159:ℚ)/23640000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3567317287:ℚ)/10000000000),((6898150273555885310694383540863382077082501835696004584181:ℚ)/102414358558800000000000000000000000000000000000000000000000),((-241951479130507476550173907:ℚ)/591462400000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((7361258993:ℚ)/10000000000),((7914006471:ℚ)/10000000000),((15361258993:ℚ)/64800000000),((40382019413:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((502626287:ℚ)/2000000000),((1331661841296515871847134787708147907560309133572153739859509:ℚ)/18615279262500000000000000000000000000000000000000000000000000),((-20382707179516947:ℚ)/48640000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((313612943:ℚ)/400000000),((1228207441:ℚ)/1250000000),((633612943:ℚ)/3200000000),((5764622323:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((50489831514580666720324443244573449391500279583012297:ℚ)/553584375000000000000000000000000000000000000000000000),((-441275761:ℚ)/1024000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((9752684401:ℚ)/10000000000),((13639288033:ℚ)/10000000000),((5917561467:ℚ)/36800000000),((57557864099:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((69900122177040064102211416744427513886089:ℚ)/541696000000000000000000000000000000000000),((-441275761:ℚ)/1024000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC19
#check @N11Formalization.C450Source27GroupedC19.bound
#print axioms N11Formalization.C450Source27GroupedC19.valid0
#print axioms N11Formalization.C450Source27GroupedC19.valid1
#print axioms N11Formalization.C450Source27GroupedC19.valid2
#print axioms N11Formalization.C450Source27GroupedC19.valid3
#print axioms N11Formalization.C450Source27GroupedC19.valid4
#print axioms N11Formalization.C450Source27GroupedC19.valid5
#print axioms N11Formalization.C450Source27GroupedC19.valid6
#print axioms N11Formalization.C450Source27GroupedC19.valid7
#print axioms N11Formalization.C450Source27GroupedC19.valid8
#print axioms N11Formalization.C450Source27GroupedC19.valid9
#print axioms N11Formalization.C450Source27GroupedC19.valid10
#print axioms N11Formalization.C450Source27GroupedC19.valid11
#print axioms N11Formalization.C450Source27GroupedC19.bound
#print axioms N11Formalization.C450Source27GroupedC19.endpoint_checks
