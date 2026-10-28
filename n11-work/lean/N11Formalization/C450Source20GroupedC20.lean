import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((2983087879:ℚ)/5000000000),((101600437:ℚ)/156250000),((4903087879:ℚ)/17800000000),((149100437:ℚ)/387500000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6680628687:ℚ)/10000000000),((26231132858380007459455313361639357:ℚ)/460887716796875000000000000000000000),((-60111153423228443389863:ℚ)/225625000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((1288862841:ℚ)/2000000000),((3370612901:ℚ)/5000000000),((6170588523:ℚ)/22120000000),((4890612901:ℚ)/13350000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5587167093:ℚ)/10000000000),((356394061156541395600565360911011974593402992251779177067783:ℚ)/6821271507266015625000000000000000000000000000000000000000000),((-847130950967423473655027:ℚ)/3040000000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((3341610111:ℚ)/5000000000),((1744984189:ℚ)/2500000000),((15784830333:ℚ)/57200000000),((2504984189:ℚ)/6912500000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((620320773:ℚ)/1250000000),((11911647749784427506973180178589496164677074026246537791:ℚ)/231945599383544921875000000000000000000000000000000000000),((-4105139448459710472212473:ℚ)/14440000000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((865254007:ℚ)/1250000000),((354963117:ℚ)/500000000),((4035762021:ℚ)/14537500000),((506963117:ℚ)/1430000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((851187817:ℚ)/2000000000),((460160971842526691632236148862054421433589657797225933399:ℚ)/9269980635428906250000000000000000000000000000000000000000),((-503160676008748788778571:ℚ)/1732800000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((7041405571:ℚ)/10000000000),((7218569289:ℚ)/10000000000),((10881405571:ℚ)/39400000000),((10258569289:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3857919103:ℚ)/10000000000),((110342951179640358191948402271629080488927669707097042530483:ℚ)/2235645334106066894531250000000000000000000000000000000000000),((-203199092917624834150111619:ℚ)/693120000000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((7160758887:ℚ)/10000000000),((114654039:ℚ)/156250000),((33002276661:ℚ)/120100000000),((162154039:ℚ)/461718750),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((3416440667:ℚ)/10000000000),((2091589886224250604917458939474801209015734053171045951501:ℚ)/42593154263802194595336914062500000000000000000000000000000),((-400640426389151989584577:ℚ)/1353750000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((7280092973:ℚ)/10000000000),((7457130797:ℚ)/10000000000),((33360278919:ℚ)/122000000000),((10497130797:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((582351743:ℚ)/2000000000),((15387332664423295661118351958778396917123510085941935679477:ℚ)/314744927701220703125000000000000000000000000000000000000000),((-69016901701523122661038617:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((231231523:ℚ)/312500000),((7695627771:ℚ)/10000000000),((1053694569:ℚ)/3931250000),((10735627771:ℚ)/30500000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((2302629591:ℚ)/10000000000),((435015154422707244630156505281605089074412751348780778470699:ℚ)/8769823224707031250000000000000000000000000000000000000000000),((-572631524231493:ℚ)/1900000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((1909497161:ℚ)/2500000000),((3967032967:ℚ)/5000000000),((2869497161:ℚ)/10800000000),((5487032967:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((436499689114580107383997353283619126651214497532598913207:ℚ)/8858282215869140625000000000000000000000000000000000000000),((-4910441:ℚ)/16000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((7876504817:ℚ)/10000000000),((4919979951:ℚ)/5000000000),((35149514451:ℚ)/160000000000),((6439979951:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((145484047808923219592765995089927604545817378517014453:ℚ)/2491129687500000000000000000000000000000000000000000000),((-4910441:ℚ)/16000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((1956577649:ℚ)/2000000000),((2729373161:ℚ)/2000000000),((2724577649:ℚ)/14720000000),((3337373161:ℚ)/8000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2501079037102883696277858953595136667:ℚ)/33856000000000000000000000000000000000),((-4910441:ℚ)/16000000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source20 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC20
#check @N11Formalization.C450Source20GroupedC20.bound
#print axioms N11Formalization.C450Source20GroupedC20.valid0
#print axioms N11Formalization.C450Source20GroupedC20.valid1
#print axioms N11Formalization.C450Source20GroupedC20.valid2
#print axioms N11Formalization.C450Source20GroupedC20.valid3
#print axioms N11Formalization.C450Source20GroupedC20.valid4
#print axioms N11Formalization.C450Source20GroupedC20.valid5
#print axioms N11Formalization.C450Source20GroupedC20.valid6
#print axioms N11Formalization.C450Source20GroupedC20.valid7
#print axioms N11Formalization.C450Source20GroupedC20.valid8
#print axioms N11Formalization.C450Source20GroupedC20.valid9
#print axioms N11Formalization.C450Source20GroupedC20.valid10
#print axioms N11Formalization.C450Source20GroupedC20.bound
#print axioms N11Formalization.C450Source20GroupedC20.endpoint_checks
