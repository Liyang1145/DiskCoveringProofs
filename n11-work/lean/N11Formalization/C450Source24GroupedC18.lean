import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((752180047:ℚ)/1250000000),((656196683:ℚ)/1000000000),((837393349:ℚ)/4450000000),((1392196683:ℚ)/4960000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6570975043:ℚ)/10000000000),((15883607065595110605726564340798522171:ℚ)/120818949632000000000000000000000000000),((-233044447557362489367731:ℚ)/739328000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((6497295363:ℚ)/10000000000),((6801477323:ℚ)/10000000000),((20577295363:ℚ)/110600000000),((4720492441:ℚ)/17800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1363560579:ℚ)/2500000000),((25440537709041407268615244530193436651650660975787267825327:ℚ)/204670124925000000000000000000000000000000000000000000000000),((-24906080715070315603527091:ℚ)/73932800000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((6736969149:ℚ)/10000000000),((3460590509:ℚ)/5000000000),((20816969149:ℚ)/112500000000),((7140590509:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1202982933:ℚ)/2500000000),((13265750557277782353564368830772489422023303445847571031:ℚ)/109200434765625000000000000000000000000000000000000000000),((-6426146051149147550839299:ℚ)/18483200000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((6856750249:ℚ)/10000000000),((880106583:ℚ)/1250000000),((20936750249:ℚ)/114400000000),((1800106583:ℚ)/7031250000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4459438401:ℚ)/10000000000),((21504524361277847517727255732415152308165232108343389277929:ℚ)/177709114551544189453125000000000000000000000000000000000000),((-1222279767351079617388993:ℚ)/3465600000000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((3488248333:ℚ)/5000000000),((7160493857:ℚ)/10000000000),((10528248333:ℚ)/58150000000),((14520493857:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4078893919:ℚ)/10000000000),((23850805467166717287188579361265932501720035282886663793003803:ℚ)/197759586889150000000000000000000000000000000000000000000000000),((-26444954914435585294234571:ℚ)/73932800000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((7096210129:ℚ)/10000000000),((3640053043:ℚ)/5000000000),((21176210129:ℚ)/118200000000),((7320053043:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1830761073:ℚ)/5000000000),((268865562629138763477093445546725108498679785404791538630219:ℚ)/2235645334106066894531250000000000000000000000000000000000000),((-6703387499771342238943171:ℚ)/18483200000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((1803973063:ℚ)/2500000000),((375962457:ℚ)/500000000),((5323973063:ℚ)/30500000000),((743962457:ℚ)/2955000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3192868597:ℚ)/10000000000),((109245438934744614704046085735882844579529536028655031521:ℚ)/900126198270703125000000000000000000000000000000000000000),((-203411993259206180938513:ℚ)/554496000000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((931896053:ℚ)/1250000000),((7997243479:ℚ)/10000000000),((2691896053:ℚ)/16200000000),((15357243479:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((488845869:ℚ)/2500000000),((143575897498212813676395618470786519305681151154590389542101:ℚ)/1163454953906250000000000000000000000000000000000000000000000),((-11485507621805469:ℚ)/30400000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((7933405119:ℚ)/10000000000),((9906356587:ℚ)/10000000000),((22013405119:ℚ)/160000000000),((17266356587:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((21412420849222677748930230660056833005306023645562158179:ℚ)/159432300000000000000000000000000000000000000000000000000),((-49252749:ℚ)/128000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((307601691:ℚ)/312500000),((6858511637:ℚ)/5000000000),((747601691:ℚ)/6900000000),((10538511637:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((6196025191601431250418266305143690254509:ℚ)/38088000000000000000000000000000000000000),((-49252749:ℚ)/128000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
private theorem node0_2 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_10
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_10
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9]
theorem packet_count : packets.length = 10 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC18
#check @N11Formalization.C450Source24GroupedC18.bound
#print axioms N11Formalization.C450Source24GroupedC18.valid0
#print axioms N11Formalization.C450Source24GroupedC18.valid1
#print axioms N11Formalization.C450Source24GroupedC18.valid2
#print axioms N11Formalization.C450Source24GroupedC18.valid3
#print axioms N11Formalization.C450Source24GroupedC18.valid4
#print axioms N11Formalization.C450Source24GroupedC18.valid5
#print axioms N11Formalization.C450Source24GroupedC18.valid6
#print axioms N11Formalization.C450Source24GroupedC18.valid7
#print axioms N11Formalization.C450Source24GroupedC18.valid8
#print axioms N11Formalization.C450Source24GroupedC18.valid9
#print axioms N11Formalization.C450Source24GroupedC18.bound
#print axioms N11Formalization.C450Source24GroupedC18.endpoint_checks
