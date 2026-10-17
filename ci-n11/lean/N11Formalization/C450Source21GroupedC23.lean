import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC23
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((3:ℚ)/8),((7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/8),((7:ℚ)/16),((726015589:ℚ)/1250000000),((6352714217:ℚ)/10000000000),((2938046767:ℚ)/6675000000),((57268999519:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3504772481:ℚ)/5000000000),((710228562665168143733587:ℚ)/22277812500000000000000000),((-5080968826710330514409603443:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((392882671:ℚ)/625000000),((6591502111:ℚ)/10000000000),((1558648013:ℚ)/3456250000),((19646838259:ℚ)/35600000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1492074863:ℚ)/2500000000),((413363940359150231272805912597349:ℚ)/17065234375000000000000000000000000),((-5218557380260703877174148227:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((3:ℚ)/8),((7:ℚ)/16),((6524965907:ℚ)/10000000000),((3415101897:ℚ)/5000000000),((25654897721:ℚ)/57200000000),((30305713279:ℚ)/55300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5383650027:ℚ)/10000000000),((29427445905187578098990586506015699:ℚ)/1258400000000000000000000000000000000),((-3955581015652311688766209049:ℚ)/11089920000000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((6763719137:ℚ)/10000000000),((3474762487:ℚ)/5000000000),((26371157411:ℚ)/58150000000),((30723337409:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1183830503:ℚ)/2500000000),((172365936841831641227816258848291299:ℚ)/8453556250000000000000000000000000000),((-1335508351165026058680868403:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((6883064809:ℚ)/10000000000),((3534413831:ℚ)/5000000000),((26729194427:ℚ)/59100000000),((31140896817:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4378474507:ℚ)/10000000000),((58730955109675317741850442011016921:ℚ)/2910675000000000000000000000000000000),((-1342305477990695650794801107:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((700239119:ℚ)/1000000000),((1437622549:ℚ)/2000000000),((2708717357:ℚ)/6005000000),((12623357843:ℚ)/23640000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1996063961:ℚ)/5000000000),((3606492076449602935754040020353049:ℚ)/180300125000000000000000000000000000),((-215847178352047753838126187:ℚ)/591462400000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/8),((7:ℚ)/16),((3560849603:ℚ)/5000000000),((1826845263:ℚ)/2500000000),((13722548809:ℚ)/30500000000),((15987916841:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1783335977:ℚ)/5000000000),((92386530269760446579633763699703521:ℚ)/4651250000000000000000000000000000000),((-1016794943100180014641959209:ℚ)/2772480000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((3620494861:ℚ)/5000000000),((1886467601:ℚ)/2500000000),((13901484583:ℚ)/31450000000),((16405273207:ℚ)/30500000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((3085931289:ℚ)/10000000000),((54170249979150327757575265167902461:ℚ)/2472756250000000000000000000000000000),((-339700145567036629624154787:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/8),((7:ℚ)/16),((1495904291:ℚ)/2000000000),((7784301397:ℚ)/10000000000),((5703712873:ℚ)/12960000000),((67290109779:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((44573677:ℚ)/250000000),((18227041852281736625841633396261737:ℚ)/839808000000000000000000000000000000),((-4530929162981751:ℚ)/12160000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/8),((7:ℚ)/16),((7717992313:ℚ)/10000000000),((9690150377:ℚ)/10000000000),((29233976939:ℚ)/80000000000),((80631052639:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((347777912847769281157117656056627153:ℚ)/8000000000000000000000000000000000000),((-76876533:ℚ)/204800000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/8),((7:ℚ)/16),((1924818287:ℚ)/2000000000),((13497003667:ℚ)/10000000000),((6990454861:ℚ)/22080000000),((107279025669:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((16842354515022281976204043:ℚ)/243763200000000000000000000),((-76876533:ℚ)/204800000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC23
#check @N11Formalization.C450Source21GroupedC23.bound
#print axioms N11Formalization.C450Source21GroupedC23.valid0
#print axioms N11Formalization.C450Source21GroupedC23.valid1
#print axioms N11Formalization.C450Source21GroupedC23.valid2
#print axioms N11Formalization.C450Source21GroupedC23.valid3
#print axioms N11Formalization.C450Source21GroupedC23.valid4
#print axioms N11Formalization.C450Source21GroupedC23.valid5
#print axioms N11Formalization.C450Source21GroupedC23.valid6
#print axioms N11Formalization.C450Source21GroupedC23.valid7
#print axioms N11Formalization.C450Source21GroupedC23.valid8
#print axioms N11Formalization.C450Source21GroupedC23.valid9
#print axioms N11Formalization.C450Source21GroupedC23.valid10
#print axioms N11Formalization.C450Source21GroupedC23.bound
#print axioms N11Formalization.C450Source21GroupedC23.endpoint_checks
