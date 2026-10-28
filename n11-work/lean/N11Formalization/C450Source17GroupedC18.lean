import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((760924769:ℚ)/1250000000),((6610584783:ℚ)/10000000000),((1960924769:ℚ)/13350000000),((11730584783:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((160469237:ℚ)/250000000),((57668243296325875418250742228902641583203:ℚ)/1087370546688000000000000000000000000000000),((-884544708185119579444982599:ℚ)/5544960000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((820591139:ℚ)/1250000000),((684901309:ℚ)/1000000000),((288655877:ℚ)/1975000000),((398967103:ℚ)/1780000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((528071977:ℚ)/1000000000),((16603153677253664282327662726398910913827904962050639083:ℚ)/329978364675000000000000000000000000000000000000000000000),((-3135134622189612173104757:ℚ)/18483200000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((1360654731:ℚ)/2000000000),((3484101797:ℚ)/5000000000),((1093551577:ℚ)/7500000000),((6044101797:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((923978569:ℚ)/2000000000),((4181401100146262582492627799840670870428191120157130637:ℚ)/84933671484375000000000000000000000000000000000000000000),((-80709213987443253335815173:ℚ)/462080000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((6922519299:ℚ)/10000000000),((7087379387:ℚ)/10000000000),((115542093:ℚ)/800000000),((12207379387:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4254385977:ℚ)/10000000000),((27219925200856905271040393996688143828558593154803109581:ℚ)/556182861328125000000000000000000000000000000000000000000),((-327408805788749056289767493:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((3520874189:ℚ)/5000000000),((1801635299:ℚ)/2500000000),((8320874189:ℚ)/58150000000),((3081635299:ℚ)/14300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((964180057:ℚ)/2500000000),((451241467536739669062744121135582789953046031072443043137199:ℚ)/9269980635428906250000000000000000000000000000000000000000000),((-20748572450196125181250997:ℚ)/115520000000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((7160961713:ℚ)/10000000000),((7325689699:ℚ)/10000000000),((16760961713:ℚ)/118200000000),((12445689699:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3415644019:ℚ)/10000000000),((288792311576876509678487972544662267474217090238903931728597:ℚ)/5961720890949511718750000000000000000000000000000000000000000),((-336541948878284366698617397:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((7280160067:ℚ)/10000000000),((7444825531:ℚ)/10000000000),((16880160067:ℚ)/120100000000),((4188275177:ℚ)/19700000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1455725591:ℚ)/5000000000),((4986165978354341879055477182907391278785103527186951350760437:ℚ)/103384628067871875000000000000000000000000000000000000000000000),((-341103205190193054730165317:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((7399344157:ℚ)/10000000000),((7563949289:ℚ)/10000000000),((16999344157:ℚ)/122000000000),((12683949289:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1151500933:ℚ)/5000000000),((120964991500476521124430709717768992362304779504922501184047:ℚ)/2517959421609765625000000000000000000000000000000000000000000),((-345660956680646364187596637:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((1503702931:ℚ)/2000000000),((8040334257:ℚ)/10000000000),((3423702931:ℚ)/25920000000),((13160334257:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((732835939:ℚ)/5000000000),((56823418892088339784871439175419980809101004595590312470199:ℚ)/1163454953906250000000000000000000000000000000000000000000000),((-1843933812402329:ℚ)/9728000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((7995072753:ℚ)/10000000000),((2486138553:ℚ)/2500000000),((17595072753:ℚ)/160000000000),((3766138553:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((127736749950595803578519352450716653890259310426868997:ℚ)/2491129687500000000000000000000000000000000000000000000),((-24486899:ℚ)/128000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((1979963927:ℚ)/2000000000),((13749501353:ℚ)/10000000000),((169563649:ℚ)/1920000000),((18869501353:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((34408775068037791485842365617888094453:ℚ)/576000000000000000000000000000000000000),((-24486899:ℚ)/128000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC18
#check @N11Formalization.C450Source17GroupedC18.bound
#print axioms N11Formalization.C450Source17GroupedC18.valid0
#print axioms N11Formalization.C450Source17GroupedC18.valid1
#print axioms N11Formalization.C450Source17GroupedC18.valid2
#print axioms N11Formalization.C450Source17GroupedC18.valid3
#print axioms N11Formalization.C450Source17GroupedC18.valid4
#print axioms N11Formalization.C450Source17GroupedC18.valid5
#print axioms N11Formalization.C450Source17GroupedC18.valid6
#print axioms N11Formalization.C450Source17GroupedC18.valid7
#print axioms N11Formalization.C450Source17GroupedC18.valid8
#print axioms N11Formalization.C450Source17GroupedC18.valid9
#print axioms N11Formalization.C450Source17GroupedC18.valid10
#print axioms N11Formalization.C450Source17GroupedC18.bound
#print axioms N11Formalization.C450Source17GroupedC18.endpoint_checks
