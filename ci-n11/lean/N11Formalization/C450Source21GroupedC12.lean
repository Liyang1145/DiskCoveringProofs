import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((3173087879:ℚ)/5000000000),((664248827:ℚ)/1000000000),((-421048827:ℚ)/1984000000),((-1573087879:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2913107561:ℚ)/5000000000),((46905184564535318572981215447693005652588142779371742721:ℚ)/413507531738281250000000000000000000000000000000000000000),((-734253686531237524170263:ℚ)/57760000000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((131706069:ℚ)/200000000),((860200061:ℚ)/1250000000),((-556200061:ℚ)/2575000000),((-67706069:ℚ)/534000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5226742509:ℚ)/10000000000),((918710579443668000315345581258657851870365386026001:ℚ)/8168828287500000000000000000000000000000000000000000),((-5832115341596365484269:ℚ)/277248000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((1364862841:ℚ)/2000000000),((1400222783:ℚ)/2000000000),((-913822783:ℚ)/4272000000),((-724862841:ℚ)/5435000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((911477731:ℚ)/2000000000),((29533797480454624994887643738472312438990198071916693923:ℚ)/267910616641406250000000000000000000000000000000000000000),((-271689050855054976341783:ℚ)/9241600000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((6943779611:ℚ)/10000000000),((1780150217:ℚ)/2500000000),((-1172150217:ℚ)/5435000000),((-3743779611:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((130815343:ℚ)/312500000),((246612955050939959652448065145385546036582027481222889077:ℚ)/2243959396960449218750000000000000000000000000000000000000),((-7761711586633693756131503:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((3531610111:ℚ)/5000000000),((7240062703:ℚ)/10000000000),((-4808062703:ℚ)/22120000000),((-643870037:ℚ)/4687500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3780908603:ℚ)/10000000000),((152392574192555340251014833996051400574126037780231181:ℚ)/1390557736158370971679687500000000000000000000000000000),((-2183372481866592020034503:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((1795659327:ℚ)/2500000000),((459968793:ℚ)/625000000),((-307968793:ℚ)/1406250000),((-76589179:ℚ)/550000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((332945243:ℚ)/1000000000),((1022951553941631395318415238475421480161325777294739:ℚ)/9358593750000000000000000000000000000000000000000000),((-1820169396238067536678741:ℚ)/43320000000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((912754007:ℚ)/1250000000),((1869729001:ℚ)/2500000000),((-97056077:ℚ)/440000000),((-512754007:ℚ)/3634375000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2809455829:ℚ)/10000000000),((359886714567499032644411335373130894477823872713207813:ℚ)/3300364535713195800781250000000000000000000000000000000),((-166936881096340737724407:ℚ)/3610000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((7421405571:ℚ)/10000000000),((7598309757:ℚ)/10000000000),((-5166309757:ℚ)/23260000000),((-4221405571:ℚ)/29550000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2172182501:ℚ)/10000000000),((188953913563855266053119090739432862218311143179302347931:ℚ)/1736634531054687500000000000000000000000000000000000000000),((-34988005291504323635195389:ℚ)/693120000000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((7540758887:ℚ)/10000000000),((1959259161:ℚ)/2500000000),((-1351259161:ℚ)/5910000000),((-4340758887:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1249402347:ℚ)/10000000000),((11508594350713462245052537584718531309443993873553138033577:ℚ)/104801383593750000000000000000000000000000000000000000000000),((-12643701414778063382705367:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((243106523:ℚ)/312500000),((8314273063:ℚ)/10000000000),((-5882273063:ℚ)/24400000000),((-143106523:ℚ)/1012500000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((4909855658087578085019916779049140752494827498527087:ℚ)/43969592285156250000000000000000000000000000000000000),((-227347:ℚ)/4000000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((8256504817:ℚ)/10000000000),((10221083193:ℚ)/10000000000),((-7789083193:ℚ)/25920000000),((-5056504817:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3963428509678817213231892320580866124312561331984161405737:ℚ)/32400000000000000000000000000000000000000000000000000000000),((-227347:ℚ)/4000000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((2032577649:ℚ)/2000000000),((14029060203:ℚ)/10000000000),((-11597060203:ℚ)/32000000000),((-1392577649:ℚ)/11040000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((290310691848586267906048041752379569945729512409158801:ℚ)/2102457600000000000000000000000000000000000000000000000),((-227347:ℚ)/4000000)⟩
theorem valid11 : Valid source21 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source21 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC12
#check @N11Formalization.C450Source21GroupedC12.bound
#print axioms N11Formalization.C450Source21GroupedC12.valid0
#print axioms N11Formalization.C450Source21GroupedC12.valid1
#print axioms N11Formalization.C450Source21GroupedC12.valid2
#print axioms N11Formalization.C450Source21GroupedC12.valid3
#print axioms N11Formalization.C450Source21GroupedC12.valid4
#print axioms N11Formalization.C450Source21GroupedC12.valid5
#print axioms N11Formalization.C450Source21GroupedC12.valid6
#print axioms N11Formalization.C450Source21GroupedC12.valid7
#print axioms N11Formalization.C450Source21GroupedC12.valid8
#print axioms N11Formalization.C450Source21GroupedC12.valid9
#print axioms N11Formalization.C450Source21GroupedC12.valid10
#print axioms N11Formalization.C450Source21GroupedC12.valid11
#print axioms N11Formalization.C450Source21GroupedC12.bound
#print axioms N11Formalization.C450Source21GroupedC12.endpoint_checks
