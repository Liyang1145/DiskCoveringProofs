import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((630235201:ℚ)/1000000000),((6600862503:ℚ)/10000000000),((-3240862503:ℚ)/24800000000),((-482705603:ℚ)/10300000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1482549279:ℚ)/2500000000),((9239896120265386325741850923405949569818030408275166141:ℚ)/52928964062500000000000000000000000000000000000000000000),((-2162478099661652364546571:ℚ)/18483200000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((3270951923:ℚ)/5000000000),((1710098657:ℚ)/2500000000),((-870098657:ℚ)/6437500000),((-2772855769:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((2670011969:ℚ)/5000000000),((353787059157926794861783008744230510905572826214998951997:ℚ)/2042207071875000000000000000000000000000000000000000000000),((-59320128660048860123217859:ℚ)/462080000000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((6781307909:ℚ)/10000000000),((6960106757:ℚ)/10000000000),((-3600106757:ℚ)/26700000000),((-6263923727:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2342159571:ℚ)/5000000000),((91460095679332435386429322647443407281164650833246346447813:ℚ)/535821233282812500000000000000000000000000000000000000000000),((-258422725558798721313948051:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((1725239861:ℚ)/2500000000),((44248659:ℚ)/62500000),((-23248659:ℚ)/169843750),((-236531369:ℚ)/3950000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4322607681:ℚ)/10000000000),((278425413256696993746810147107142785078256250421615791:ℚ)/1635538919067382812500000000000000000000000000000000000),((-16814703866580433219011891:ℚ)/115520000000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((7020579663:ℚ)/10000000000),((3599716199:ℚ)/5000000000),((-1919716199:ℚ)/13825000000),((-6981738989:ℚ)/112500000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3930100593:ℚ)/10000000000),((816131794046985305038509332906720882755730921665077695461:ℚ)/4805767536163330078125000000000000000000000000000000000000),((-279675593500018894023792299:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((285606807:ℚ)/400000000),((1463809847:ℚ)/2000000000),((-791809847:ℚ)/5625000000),((-293620421:ℚ)/4576000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3496400573:ℚ)/10000000000),((20757814375342254499409686556447733329862763395495047:ℚ)/122497689600000000000000000000000000000000000000000000),((-464550144309356703659579:ℚ)/2957312000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((7259732481:ℚ)/10000000000),((929829681:ℚ)/1250000000),((-509829681:ℚ)/3575000000),((-7699197443:ℚ)/116300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3003670369:ℚ)/10000000000),((59443664676198786278829850373029744204270607358827822590557:ℚ)/351475621595312500000000000000000000000000000000000000000000),((-301040113650122183582574731:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((7379267981:ℚ)/10000000000),((1889549609:ℚ)/2500000000),((-1049549609:ℚ)/7268750000),((-8057803943:ℚ)/118200000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((120800197:ℚ)/500000000),((4691266568328549894344324622220345810129308988049440564759:ℚ)/27786152496875000000000000000000000000000000000000000000000),((-311764518039706704894145731:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((3749388993:ℚ)/5000000000),((1559448779:ℚ)/2000000000),((-887448779:ℚ)/5910000000),((-4208166979:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1633912857:ℚ)/10000000000),((35608326066439487331198451587711794271790528958541498231397:ℚ)/209602767187500000000000000000000000000000000000000000000000),((-80629287736843259978074379:ℚ)/462080000000000000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((773772633:ℚ)/1000000000),((2068765131:ℚ)/2500000000),((-1228765131:ℚ)/7625000000),((-913317899:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((3963287852886702494903532564183217349996438626098413983:ℚ)/23052729600000000000000000000000000000000000000000000000),((-22967329:ℚ)/128000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((2053841527:ℚ)/2500000000),((5091816939:ℚ)/5000000000),((-379090771:ℚ)/1800000000),((-2641524581:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((166162991389846314282757922192021931137518779537446635597:ℚ)/900000000000000000000000000000000000000000000000000000000),((-22967329:ℚ)/128000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((10123402177:ℚ)/10000000000),((13993670537:ℚ)/10000000000),((-10633670537:ℚ)/40000000000),((-16290206531:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((874257990759152917197692978389003941853987524731113340923:ℚ)/4204915200000000000000000000000000000000000000000000000000),((-22967329:ℚ)/128000000)⟩
theorem valid11 : Valid source23 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC13
#check @N11Formalization.C450Source23GroupedC13.bound
#print axioms N11Formalization.C450Source23GroupedC13.valid0
#print axioms N11Formalization.C450Source23GroupedC13.valid1
#print axioms N11Formalization.C450Source23GroupedC13.valid2
#print axioms N11Formalization.C450Source23GroupedC13.valid3
#print axioms N11Formalization.C450Source23GroupedC13.valid4
#print axioms N11Formalization.C450Source23GroupedC13.valid5
#print axioms N11Formalization.C450Source23GroupedC13.valid6
#print axioms N11Formalization.C450Source23GroupedC13.valid7
#print axioms N11Formalization.C450Source23GroupedC13.valid8
#print axioms N11Formalization.C450Source23GroupedC13.valid9
#print axioms N11Formalization.C450Source23GroupedC13.valid10
#print axioms N11Formalization.C450Source23GroupedC13.valid11
#print axioms N11Formalization.C450Source23GroupedC13.bound
#print axioms N11Formalization.C450Source23GroupedC13.endpoint_checks
