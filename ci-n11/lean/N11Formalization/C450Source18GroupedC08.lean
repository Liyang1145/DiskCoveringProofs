import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((1623794027:ℚ)/2500000000),((6795402037:ℚ)/10000000000),((-50918618333:ℚ)/99200000000),((-1283794027:ℚ)/3218750000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1364903757:ℚ)/2500000000),((668151502024640143803478483127492519423068735951971677:ℚ)/9691582775115966796875000000000000000000000000000000000),((10377937338072063926307079:ℚ)/46208000000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((6733595421:ℚ)/10000000000),((691459923:ℚ)/1000000000),((-5199139307:ℚ)/10300000000),((-5373595421:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4821514037:ℚ)/10000000000),((12083964486269844461254436605492124016436826298519394121:ℚ)/181419413523864746093750000000000000000000000000000000000),((454153046714396417739231:ℚ)/2048000000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((3426389981:ℚ)/5000000000),((879222553:ℚ)/1250000000),((-6633002977:ℚ)/13112500000),((-915463327:ℚ)/2225000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4471535191:ℚ)/10000000000),((601298577040984452260459478644107777455164460238220941:ℚ)/9027251965332031250000000000000000000000000000000000000),((40723541939704172599723511:ℚ)/184832000000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((43574681:ℚ)/62500000),((7093365289:ℚ)/10000000000),((-53600287601:ℚ)/106800000000),((-70149362:ℚ)/168359375),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1023488181:ℚ)/2500000000),((8155180657494161380783440865725197635857238332659:ℚ)/124429460830288007855415344238281250000000000000000),((6321677284379350604911:ℚ)/28880000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((7031527889:ℚ)/10000000000),((3576473233:ℚ)/5000000000),((-27068259097:ℚ)/53875000000),((-5671527889:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1946156493:ℚ)/5000000000),((221484035645641853659592539989994090160285911920782364397:ℚ)/3378671458697509765625000000000000000000000000000000000000),((161303766866473250939773471:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((1772775809:ℚ)/2500000000),((1803131013:ℚ)/2500000000),((-13668179117:ℚ)/27175000000),((-1432775809:ℚ)/3426562500),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3680244939:ℚ)/10000000000),((746706696594504008107576948107550723964290744208151083:ℚ)/11388703667083382606506347656250000000000000000000000000),((10048222272658435059645631:ℚ)/46208000000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((7150675093:ℚ)/10000000000),((363604907:ℚ)/500000000),((-2760444163:ℚ)/5482500000),((-827239299:ℚ)/1975000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3455824757:ℚ)/10000000000),((684748803523324066939635490097888314314354587212871:ℚ)/10441980743408203125000000000000000000000000000000000),((160238306337089329038356999:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7210243553:ℚ)/10000000000),((7331668821:ℚ)/10000000000),((-55745019389:ℚ)/110600000000),((-5850243553:ℚ)/13943750000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3216463131:ℚ)/10000000000),((2743534561735405379292023694578407930682638521980701981:ℚ)/41830773300600051879882812500000000000000000000000000000),((159704016143325668012476159:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-9:ℚ)/16),((-1:ℚ)/2),((7269808701:ℚ)/10000000000),((369561809:ℚ)/500000000),((-2814056281:ℚ)/5577500000),((-5909808701:ℚ)/14062500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((184908161:ℚ)/625000000),((14903656580985863210725796412094846846271807401905456059:ℚ)/227205315604805946350097656250000000000000000000000000000),((159168685199707615133866551:ℚ)/739328000000000000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((7329370623:ℚ)/10000000000),((751036127:ℚ)/1000000000),((-5735325143:ℚ)/11250000000),((-5969370623:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((167291133:ℚ)/625000000),((5476425591286431803081473512003689843067991608371596669:ℚ)/82243321875000000000000000000000000000000000000000000000),((158632312909564400739148479:ℚ)/739328000000000000000000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((744848511:ℚ)/1000000000),((7748575111:ℚ)/10000000000),((-59497175999:ℚ)/114400000000),((-608848511:ℚ)/1477500000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2000138297:ℚ)/10000000000),((2740928619668028522259680447854764376678658557076731:ℚ)/40037414758300781250000000000000000000000000000000000),((1575564420802192123214271:ℚ)/7393280000000000000000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-9:ℚ)/16),((-1:ℚ)/2),((3843339389:ℚ)/5000000000),((3993372147:ℚ)/5000000000),((-30820349323:ℚ)/59100000000),((-3163339389:ℚ)/7625000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((55953340565972452565003072631518203581728200767113330497:ℚ)/818760809326171875000000000000000000000000000000000000000),((54079549:ℚ)/256000000)⟩
theorem valid11 : Valid source18 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((1584965811:ℚ)/2000000000),((1692592897:ℚ)/2000000000),((-13185336073:ℚ)/24400000000),((-1312965811:ℚ)/3240000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((154576061940448014535645943013640196058206463481878911:ℚ)/2161193400000000000000000000000000000000000000000000000),((54079549:ℚ)/256000000)⟩
theorem valid12 : Valid source18 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((1680202957:ℚ)/2000000000),((5183341403:ℚ)/5000000000),((-41530072627:ℚ)/64800000000),((-1408202957:ℚ)/4000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((222874896849759620301628107737843179036876397032508929547:ℚ)/2550916800000000000000000000000000000000000000000000000000),((54079549:ℚ)/256000000)⟩
theorem valid13 : Valid source18 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((10304628183:ℚ)/10000000000),((7085521287:ℚ)/5000000000),((-58649691583:ℚ)/80000000000),((-8944628183:ℚ)/27600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((202285311880995002958926588643959910314220251249682604085701:ℚ)/1904400000000000000000000000000000000000000000000000000000000),((54079549:ℚ)/256000000)⟩
theorem valid14 : Valid source18 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source18 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC08
#check @N11Formalization.C450Source18GroupedC08.bound
#print axioms N11Formalization.C450Source18GroupedC08.valid0
#print axioms N11Formalization.C450Source18GroupedC08.valid1
#print axioms N11Formalization.C450Source18GroupedC08.valid2
#print axioms N11Formalization.C450Source18GroupedC08.valid3
#print axioms N11Formalization.C450Source18GroupedC08.valid4
#print axioms N11Formalization.C450Source18GroupedC08.valid5
#print axioms N11Formalization.C450Source18GroupedC08.valid6
#print axioms N11Formalization.C450Source18GroupedC08.valid7
#print axioms N11Formalization.C450Source18GroupedC08.valid8
#print axioms N11Formalization.C450Source18GroupedC08.valid9
#print axioms N11Formalization.C450Source18GroupedC08.valid10
#print axioms N11Formalization.C450Source18GroupedC08.valid11
#print axioms N11Formalization.C450Source18GroupedC08.valid12
#print axioms N11Formalization.C450Source18GroupedC08.valid13
#print axioms N11Formalization.C450Source18GroupedC08.valid14
#print axioms N11Formalization.C450Source18GroupedC08.bound
#print axioms N11Formalization.C450Source18GroupedC08.endpoint_checks
