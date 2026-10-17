import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/8),((3:ℚ)/16),((1172384491:ℚ)/2000000000),((618878491:ℚ)/1000000000),((3028384491:ℚ)/10300000000),((3776635473:ℚ)/9920000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3449532043:ℚ)/5000000000),((-1064098407574416058905711204078588888685854447405870417:ℚ)/6829543750000000000000000000000000000000000000000000000),((-44254181010132258693243129:ℚ)/147865600000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((6103667413:ℚ)/10000000000),((3215016161:ℚ)/5000000000),((15383667413:ℚ)/53400000000),((19245048483:ℚ)/51500000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((6382927789:ℚ)/10000000000),((-1333410060377070237085570802493782700593147950467562957:ℚ)/8812112500000000000000000000000000000000000000000000000),((-1125957550839711692846526689:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((396568921:ℚ)/625000000),((1637638887:ℚ)/2500000000),((976568921:ℚ)/3396875000),((3237638887:ℚ)/8900000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2914390329:ℚ)/5000000000),((-36894146827553973885260385355481825470562106244792907:ℚ)/244973278617858886718750000000000000000000000000000000),((-288402393137620450108869521:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((3232857381:ℚ)/5000000000),((3335508263:ℚ)/5000000000),((7872857381:ℚ)/27650000000),((19606524789:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((5533819609:ℚ)/10000000000),((-43819829535728185482641427371719748312161961100150089:ℚ)/294908581542968750000000000000000000000000000000000000),((-1162986040847041812693135121:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((6586261353:ℚ)/10000000000),((6791418499:ℚ)/10000000000),((15866261353:ℚ)/56250000000),((71562849:ℚ)/200000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2612108557:ℚ)/5000000000),((-23603124252734889701910654994918659713646368183743097:ℚ)/160932540893554687500000000000000000000000000000000000),((-4688793248745351227699034409:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((3353372961:ℚ)/5000000000),((863970561:ℚ)/1250000000),((7993372961:ℚ)/28600000000),((1663970561:ℚ)/4687500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2448579067:ℚ)/5000000000),((-21175589303906831041489220971792022661015531091775153147:ℚ)/146210350000000000000000000000000000000000000000000000000),((-73827931449055919299137889:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((6827171649:ℚ)/10000000000),((1758014327:ℚ)/2500000000),((16107171649:ℚ)/58150000000),((10074042981:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1137209663:ℚ)/2500000000),((-175832762359482900767817010528555260977727344817403938427:ℚ)/1228935739843750000000000000000000000000000000000000000000),((-297533073836288877715230961:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((6947541497:ℚ)/10000000000),((7152299589:ℚ)/10000000000),((5409180499:ℚ)/19700000000),((40656898767:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1043474303:ℚ)/2500000000),((-1689182381125457256045116440193126193453709384245477553:ℚ)/11945895312500000000000000000000000000000000000000000000),((-4795419748739573362815445689:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((7067858233:ℚ)/10000000000),((7392642207:ℚ)/10000000000),((16347858233:ℚ)/61000000000),((13792642207:ℚ)/39400000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3764342291:ℚ)/10000000000),((-194478554320218938139170685799816724407294439192183451179:ℚ)/1418631250000000000000000000000000000000000000000000000000),((-4791104020589491518724150241:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((7308342549:ℚ)/10000000000),((393640961:ℚ)/500000000),((16588342549:ℚ)/64800000000),((2140922883:ℚ)/6100000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((2779351593:ℚ)/10000000000),((-100671802170193027478915306683983520754488434762776069:ℚ)/777600000000000000000000000000000000000000000000000000),((-320220168771229439:ℚ)/972800000000000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((7788777197:ℚ)/10000000000),((2447137619:ℚ)/2500000000),((17068777197:ℚ)/80000000000),((1349045873:ℚ)/3600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-334496048093875219031360834169691485552033772762789561911:ℚ)/3200000000000000000000000000000000000000000000000000000000),((-69838207:ℚ)/204800000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((9705288261:ℚ)/10000000000),((13606924413:ℚ)/10000000000),((18985288261:ℚ)/110400000000),((60020773239:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-18577366743885145768630369325035117984649063960009865503:ℚ)/233606400000000000000000000000000000000000000000000000000),((-69838207:ℚ)/204800000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC19
#check @N11Formalization.C450Source31GroupedC19.bound
#print axioms N11Formalization.C450Source31GroupedC19.valid0
#print axioms N11Formalization.C450Source31GroupedC19.valid1
#print axioms N11Formalization.C450Source31GroupedC19.valid2
#print axioms N11Formalization.C450Source31GroupedC19.valid3
#print axioms N11Formalization.C450Source31GroupedC19.valid4
#print axioms N11Formalization.C450Source31GroupedC19.valid5
#print axioms N11Formalization.C450Source31GroupedC19.valid6
#print axioms N11Formalization.C450Source31GroupedC19.valid7
#print axioms N11Formalization.C450Source31GroupedC19.valid8
#print axioms N11Formalization.C450Source31GroupedC19.valid9
#print axioms N11Formalization.C450Source31GroupedC19.valid10
#print axioms N11Formalization.C450Source31GroupedC19.valid11
#print axioms N11Formalization.C450Source31GroupedC19.bound
#print axioms N11Formalization.C450Source31GroupedC19.endpoint_checks
