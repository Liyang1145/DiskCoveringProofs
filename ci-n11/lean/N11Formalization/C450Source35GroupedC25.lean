import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/2),((9:ℚ)/16),((1333045431:ℚ)/2500000000),((709398493:ℚ)/1250000000),((1993045431:ℚ)/3218750000),((9104586437:ℚ)/12400000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1586303807:ℚ)/2000000000),((-451516943288510259475382662996736171111027058132647084811:ℚ)/1227389200000000000000000000000000000000000000000000000000),((-802620476088046848805633:ℚ)/1805000000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((696691927:ℚ)/1250000000),((5916383887:ℚ)/10000000000),((1026691927:ℚ)/1668750000),((75007454983:ℚ)/103000000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7475452389:ℚ)/10000000000),((-167060722615748933583206904291455790904241435767331064153421:ℚ)/455872045312500000000000000000000000000000000000000000000000),((-49608605722259173219927:ℚ)/112812500000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((726826081:ℚ)/1250000000),((6036882789:ℚ)/10000000000),((1056826081:ℚ)/1698437500),((76091945101:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((6996306373:ℚ)/10000000000),((-114998636320456618536001464290251764999477732179621914183769:ℚ)/306520521200000000000000000000000000000000000000000000000000),((-198083068710554391598947:ℚ)/451250000000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((2967524777:ℚ)/5000000000),((1231464063:ℚ)/2000000000),((4287524777:ℚ)/6912500000),((15435176567:ℚ)/21740000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1349293739:ℚ)/2000000000),((-207647658437483891044038070492617920393208419345972453759:ℚ)/554886033717968750000000000000000000000000000000000000000),((-62999516810334075734739:ℚ)/144400000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/2),((9:ℚ)/16),((6055431161:ℚ)/10000000000),((3138849831:ℚ)/5000000000),((8695431161:ℚ)/14062500000),((39129648479:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1622174557:ℚ)/2500000000),((-13871304821015369075631271685633028171520820105305119719:ℚ)/37158481274414062500000000000000000000000000000000000000),((-3129991491630411012537903:ℚ)/7220000000000000000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((6175756553:ℚ)/10000000000),((792233557:ℚ)/1250000000),((8815756553:ℚ)/14181250000),((9850102013:ℚ)/14062500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1244395417:ℚ)/2000000000),((-4130440463780189862649374995608298923489944087165696457:ℚ)/10954678058624267578125000000000000000000000000000000000),((-164542042088891224790053:ℚ)/380000000000000000000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((249435963:ℚ)/400000000),((1279604761:ℚ)/2000000000),((355035963:ℚ)/572000000),((15868442849:ℚ)/22690000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((6084883851:ℚ)/10000000000),((-3931424541952551119977780223526165888902685711825493841343:ℚ)/10440457803668750000000000000000000000000000000000000000000),((-6559812704656615624183:ℚ)/15200000000000000000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((1259205721:ℚ)/2000000000),((3259147761:ℚ)/5000000000),((1787205721:ℚ)/2907500000),((40212329849:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5945068441:ℚ)/10000000000),((-45954269276059034502733228419284121208138220776364834209657:ℚ)/123667372400000000000000000000000000000000000000000000000000),((-3088131183684529327430283:ℚ)/7220000000000000000000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((3208124999:ℚ)/5000000000),((6638517403:ℚ)/10000000000),((4528124999:ℚ)/7387500000),((81506656627:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5656443673:ℚ)/10000000000),((-538634646368797050994856322880938218555101484456970660870557:ℚ)/1452602044495312500000000000000000000000000000000000000000000),((-1533127992373343458107629:ℚ)/3610000000000000000000000)⟩
theorem valid8 : Valid source35 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source35 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((102131613:ℚ)/156250000),((6758691873:ℚ)/10000000000),((286763226:ℚ)/469140625),((82588226857:ℚ)/118200000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1070835029:ℚ)/2000000000),((-382266637186324590105716153675472136632774463477456165453459:ℚ)/1032985459462500000000000000000000000000000000000000000000000),((-380468902488592333290831:ℚ)/902500000000000000000000)⟩
theorem valid9 : Valid source35 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((832068831:ℚ)/1250000000),((6878821197:ℚ)/10000000000),((1162068831:ℚ)/1906250000),((83669390773:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((5035772463:ℚ)/10000000000),((-243940065680646658310957124211020522383605814320831429950033:ℚ)/660448372881250000000000000000000000000000000000000000000000),((-47197143911379737549997:ℚ)/112812500000000000000000)⟩
theorem valid10 : Valid source35 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source35 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source35 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((1694158609:ℚ)/2500000000),((889869097:ℚ)/1250000000),((2354158609:ℚ)/3931250000),((10728821873:ℚ)/15250000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((4697920963:ℚ)/10000000000),((-1257562242663672272961670290650366963880898506208185148813:ℚ)/3485621313476562500000000000000000000000000000000000000000),((-739854975323751801680503:ℚ)/1805000000000000000000000)⟩
theorem valid11 : Valid source35 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((7016679203:ℚ)/10000000000),((1839731903:ℚ)/2500000000),((9656679203:ℚ)/16200000000),((21997587127:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((3943479991:ℚ)/10000000000),((-153221475041226565911739961809354145762800596790656908851:ℚ)/425623169531250000000000000000000000000000000000000000000),((-2908760128789581682251253:ℚ)/7220000000000000000000000)⟩
theorem valid12 : Valid source35 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source35 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((3628286237:ℚ)/5000000000),((927444513:ℚ)/1000000000),((4948286237:ℚ)/10000000000),((10523000617:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((3017691743:ℚ)/10000000000),((-1191207168524514703980293145313976469321600351603817219:ℚ)/4534963200000000000000000000000000000000000000000000000),((-7693935640658801:ℚ)/19456000000000000)⟩
theorem valid13 : Valid source35 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((573223759:ℚ)/625000000),((13092570671:ℚ)/10000000000),((738223759:ℚ)/1725000000),((139593136039:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-13733572455197143480557775744827832586497:ℚ)/70656000000000000000000000000000000000000),((-51279517:ℚ)/128000000)⟩
theorem valid14 : Valid source35 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC25
#check @N11Formalization.C450Source35GroupedC25.bound
#print axioms N11Formalization.C450Source35GroupedC25.valid0
#print axioms N11Formalization.C450Source35GroupedC25.valid1
#print axioms N11Formalization.C450Source35GroupedC25.valid2
#print axioms N11Formalization.C450Source35GroupedC25.valid3
#print axioms N11Formalization.C450Source35GroupedC25.valid4
#print axioms N11Formalization.C450Source35GroupedC25.valid5
#print axioms N11Formalization.C450Source35GroupedC25.valid6
#print axioms N11Formalization.C450Source35GroupedC25.valid7
#print axioms N11Formalization.C450Source35GroupedC25.valid8
#print axioms N11Formalization.C450Source35GroupedC25.valid9
#print axioms N11Formalization.C450Source35GroupedC25.valid10
#print axioms N11Formalization.C450Source35GroupedC25.valid11
#print axioms N11Formalization.C450Source35GroupedC25.valid12
#print axioms N11Formalization.C450Source35GroupedC25.valid13
#print axioms N11Formalization.C450Source35GroupedC25.valid14
#print axioms N11Formalization.C450Source35GroupedC25.bound
#print axioms N11Formalization.C450Source35GroupedC25.endpoint_checks
