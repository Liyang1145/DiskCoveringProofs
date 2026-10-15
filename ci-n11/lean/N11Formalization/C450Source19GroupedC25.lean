import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((5766355197:ℚ)/10000000000),((394310733:ℚ)/625000000),((7126355197:ℚ)/13350000000),((4268796597:ℚ)/6200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1418867219:ℚ)/2000000000),((289413556351200750093028133978203:ℚ)/594817593750000000000000000000000000),((-3546892662883800465103463:ℚ)/10830000000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6243402061:ℚ)/10000000000),((654736933:ℚ)/1000000000),((7603402061:ℚ)/13825000000),((26384391:ℚ)/40000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((379224487:ℚ)/625000000),((-317631513764219196888173703677738845508766253604598101:ℚ)/49544641699218750000000000000000000000000000000000000000),((-47881824290004007026539:ℚ)/144400000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((6481819383:ℚ)/10000000000),((1357141397:ℚ)/2000000000),((7841819383:ℚ)/14300000000),((2074038939:ℚ)/3160000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((274668409:ℚ)/500000000),((-127727621743763249104997263930206719955790260531972021:ℚ)/18276293750000000000000000000000000000000000000000000000),((-96210413913798540990017:ℚ)/288800000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((3360087717:ℚ)/5000000000),((6904855181:ℚ)/10000000000),((4040087717:ℚ)/7268750000),((73663696629:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2429729043:ℚ)/5000000000),((-17698921105318982060513601825655537252888235644355693:ℚ)/1800198837661743164062500000000000000000000000000000000),((-2419781407268827854173543:ℚ)/7220000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6839332373:ℚ)/10000000000),((3511995257:ℚ)/5000000000),((2733110791:ℚ)/4925000000),((37367957313:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4512283019:ℚ)/10000000000),((-5582337123546814853000104677579995132675992316698039:ℚ)/559963842773437500000000000000000000000000000000000000),((-1212604489910523572103099:ℚ)/3610000000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((1739619041:ℚ)/2500000000),((7143113597:ℚ)/10000000000),((2079619041:ℚ)/3753125000),((25269340791:ℚ)/39400000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2069130819:ℚ)/5000000000),((-3331906264315390338712723395259278733543654687937907:ℚ)/330414505195617675781250000000000000000000000000000000),((-2430574327842131346884667:ℚ)/7220000000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((1415521487:ℚ)/2000000000),((3631112503:ℚ)/5000000000),((1687521487:ℚ)/3050000000),((38440012527:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3729291103:ℚ)/10000000000),((-1804764225432413555100173475126789158726349424800381:ℚ)/177328906250000000000000000000000000000000000000000000),((-1217938749881878304057809:ℚ)/3610000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((287869071:ℚ)/400000000),((7381325281:ℚ)/10000000000),((342269071:ℚ)/619500000),((77951927529:ℚ)/122000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((3272255779:ℚ)/10000000000),((-1269316912143996371066274571259764816897440634679:ℚ)/123829096289062500000000000000000000000000000000000),((-2441118541022772200380393:ℚ)/7220000000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((457239671:ℚ)/625000000),((7500414931:ℚ)/10000000000),((542239671:ℚ)/982812500),((26341244793:ℚ)/41300000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2743192373:ℚ)/10000000000),((-59704096072769123822609360039988312444127658673:ℚ)/5794181232340633869171142578125000000000000000000),((-2446297494143297447157043:ℚ)/7220000000000000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((7434931837:ℚ)/10000000000),((7738564231:ℚ)/10000000000),((8794931837:ℚ)/16200000000),((81167078079:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((260999141:ℚ)/1250000000),((-8103822823292231395587891071506056654813977430829117:ℚ)/984150000000000000000000000000000000000000000000000000),((-165191297825767807:ℚ)/486400000000000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((7673095379:ℚ)/10000000000),((9642644943:ℚ)/10000000000),((9033095379:ℚ)/20000000000),((10922644943:ℚ)/14400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3877048927175683988590632839326849:ℚ)/300000000000000000000000000000000000),((-21846571:ℚ)/64000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((4788632761:ℚ)/5000000000),((13447429059:ℚ)/10000000000),((1822877587:ℚ)/4600000000),((132546861531:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((69436149866946014760857:ℚ)/2116000000000000000000000),((-21846571:ℚ)/64000000)⟩
theorem valid11 : Valid source19 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC25
#check @N11Formalization.C450Source19GroupedC25.bound
#print axioms N11Formalization.C450Source19GroupedC25.valid0
#print axioms N11Formalization.C450Source19GroupedC25.valid1
#print axioms N11Formalization.C450Source19GroupedC25.valid2
#print axioms N11Formalization.C450Source19GroupedC25.valid3
#print axioms N11Formalization.C450Source19GroupedC25.valid4
#print axioms N11Formalization.C450Source19GroupedC25.valid5
#print axioms N11Formalization.C450Source19GroupedC25.valid6
#print axioms N11Formalization.C450Source19GroupedC25.valid7
#print axioms N11Formalization.C450Source19GroupedC25.valid8
#print axioms N11Formalization.C450Source19GroupedC25.valid9
#print axioms N11Formalization.C450Source19GroupedC25.valid10
#print axioms N11Formalization.C450Source19GroupedC25.valid11
#print axioms N11Formalization.C450Source19GroupedC25.bound
#print axioms N11Formalization.C450Source19GroupedC25.endpoint_checks
