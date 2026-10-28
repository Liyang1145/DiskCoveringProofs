import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((152560441:ℚ)/250000000),((1322638361:ℚ)/2000000000),((77520147:ℚ)/445000000),((5375915083:ℚ)/19840000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((638568721:ℚ)/1000000000),((23370985972914053689233268598638624977:ℚ)/966551597056000000000000000000000000000),((-22901771218312600538049:ℚ)/231040000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((6578493261:ℚ)/10000000000),((3425549097:ℚ)/5000000000),((9778493261:ℚ)/55300000000),((13796647291:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((327791559:ℚ)/625000000),((19641154610935708196931869626364024586456478329250120551967:ℚ)/866193207271875000000000000000000000000000000000000000000000),((-115042420894745019675474827:ℚ)/1108992000000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((1363295093:ℚ)/2000000000),((1742510267:ℚ)/2500000000),((667765031:ℚ)/3750000000),((6987530801:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((71574491:ℚ)/156250000),((26021649043826356278495442542776997251778448397664471:ℚ)/1179634326171875000000000000000000000000000000000000000),((-1568007309303286467175721:ℚ)/14786560000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((1:ℚ)/8),((3:ℚ)/16),((1733863579:ℚ)/2500000000),((7029510077:ℚ)/10000000000),((2533863579:ℚ)/14181250000),((28128530231:ℚ)/112500000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((2106479239:ℚ)/5000000000),((6929588344585035922571599077834568324747348824029860442797543:ℚ)/318158905792236328125000000000000000000000000000000000000000000),((-2476665027181303009382089:ℚ)/23104000000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((3497470429:ℚ)/5000000000),((88612219:ℚ)/125000000),((5097470429:ℚ)/28600000000),((353836657:ℚ)/1418125000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((4017273591:ℚ)/10000000000),((316573370731094102940986044425337695351372339193219789:ℚ)/14579936190670227050781250000000000000000000000000000000),((-27589955476328926597649:ℚ)/256000000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/8),((3:ℚ)/16),((881803193:ℚ)/1250000000),((3574221719:ℚ)/5000000000),((427267731:ℚ)/2403125000),((14242665157:ℚ)/57200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3812133727:ℚ)/10000000000),((233978959555733551792843702980948614420443946534699347190709:ℚ)/10807887348293750000000000000000000000000000000000000000000000),((-625830762967453772717121:ℚ)/5776000000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((7113908417:ℚ)/10000000000),((7207907867:ℚ)/10000000000),((10313908417:ℚ)/58150000000),((28663723601:ℚ)/115350000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3595916947:ℚ)/10000000000),((25934762834638547821588294030068348853873398690841219981731:ℚ)/1201347054450236328125000000000000000000000000000000000000000),((-40266459953097941744149681:ℚ)/369664000000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/8),((3:ℚ)/16),((7173389523:ℚ)/10000000000),((7267370843:ℚ)/10000000000),((1481912789:ℚ)/8375000000),((28842112529:ℚ)/116300000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((13465941:ℚ)/40000000),((3307425615555391337720597761811508122873961720613110553:ℚ)/153616967480468750000000000000000000000000000000000000000),((-336396974294414878676243:ℚ)/3072000000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((3616434453:ℚ)/5000000000),((3663416201:ℚ)/5000000000),((5216434453:ℚ)/29550000000),((14510248603:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3120920871:ℚ)/10000000000),((16399369456635425307740864795230120372701814528320470602811:ℚ)/763626625934791564941406250000000000000000000000000000000000),((-30519822634906640155453883:ℚ)/277248000000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/8),((3:ℚ)/16),((3646173303:ℚ)/5000000000),((3693146289:ℚ)/5000000000),((5246173303:ℚ)/29787500000),((14599438867:ℚ)/59100000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((114202363:ℚ)/400000000),((3269997858307569944103188928073959796260022025972338894375657:ℚ)/152633304689051953125000000000000000000000000000000000000000000),((-30679832185349767030926083:ℚ)/277248000000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((918977833:ℚ)/1250000000),((7445751403:ℚ)/10000000000),((1098233:ℚ)/6250000),((29377254209:ℚ)/119150000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2562584657:ℚ)/10000000000),((882730506108953578191135653978642987056378219013450177:ℚ)/41297350729370117187500000000000000000000000000000000000),((-642496993544994130619681:ℚ)/5776000000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((46320607:ℚ)/62500000),((756466513:ℚ)/1000000000),((66320607:ℚ)/381250000),((2973399539:ℚ)/12010000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((279132369:ℚ)/1250000000),((54004651800936846155635013716815546251498792731647991107:ℚ)/2517959421609765625000000000000000000000000000000000000000),((-1614577773721644404921:ℚ)/14440000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((7530241373:ℚ)/10000000000),((8040271939:ℚ)/10000000000),((10730241373:ℚ)/64800000000),((31160815817:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1355938261:ℚ)/10000000000),((140029022881475251556771275856845706110284852210073478663:ℚ)/6357677343750000000000000000000000000000000000000000000000),((-41760014609649817089771641:ℚ)/369664000000000000000000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((80059613:ℚ)/100000000),((9942121899:ℚ)/10000000000),((112059613:ℚ)/800000000),((36866365697:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((421128959731517218768079253419093301715826819225820827:ℚ)/17714700000000000000000000000000000000000000000000000000),((-3636633:ℚ)/32000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((1238519493:ℚ)/1250000000),((137442923:ℚ)/100000000),((1638519493:ℚ)/13800000000),((482728769:ℚ)/1600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2885209945231188529278839339060833:ℚ)/101568000000000000000000000000000000),((-3636633:ℚ)/32000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC19
#check @N11Formalization.C450Source12GroupedC19.bound
#print axioms N11Formalization.C450Source12GroupedC19.valid0
#print axioms N11Formalization.C450Source12GroupedC19.valid1
#print axioms N11Formalization.C450Source12GroupedC19.valid2
#print axioms N11Formalization.C450Source12GroupedC19.valid3
#print axioms N11Formalization.C450Source12GroupedC19.valid4
#print axioms N11Formalization.C450Source12GroupedC19.valid5
#print axioms N11Formalization.C450Source12GroupedC19.valid6
#print axioms N11Formalization.C450Source12GroupedC19.valid7
#print axioms N11Formalization.C450Source12GroupedC19.valid8
#print axioms N11Formalization.C450Source12GroupedC19.valid9
#print axioms N11Formalization.C450Source12GroupedC19.valid10
#print axioms N11Formalization.C450Source12GroupedC19.valid11
#print axioms N11Formalization.C450Source12GroupedC19.valid12
#print axioms N11Formalization.C450Source12GroupedC19.valid13
#print axioms N11Formalization.C450Source12GroupedC19.valid14
#print axioms N11Formalization.C450Source12GroupedC19.bound
#print axioms N11Formalization.C450Source12GroupedC19.endpoint_checks
