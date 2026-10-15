import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((1471484833:ℚ)/2500000000),((803737981:ℚ)/1250000000),((757161611:ℚ)/2225000000),((1139737981:ℚ)/2480000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6849262551:ℚ)/10000000000),((32276527781904852907044673310932049:ℚ)/487173184000000000000000000000000000),((-402194851198317173914479:ℚ)/1216000000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((3182317987:ℚ)/5000000000),((6668963261:ℚ)/10000000000),((4782317987:ℚ)/13825000000),((9356963261:ℚ)/21360000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5781920143:ℚ)/10000000000),((232888749777874287486326387466636005662994174200822910909657:ℚ)/3991418299108800000000000000000000000000000000000000000000000),((-509978972730853705497371261:ℚ)/1478656000000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((1320758351:ℚ)/2000000000),((3453959061:ℚ)/5000000000),((1960758351:ℚ)/5720000000),((8676237:ℚ)/20000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5177802961:ℚ)/10000000000),((2255243099904010132327472013273304303464510304897:ℚ)/39325000000000000000000000000000000000000000000000),((-20478774043085992650642557:ℚ)/58368000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((342141823:ℚ)/500000000),((7027359587:ℚ)/10000000000),((502141823:ℚ)/1453750000),((9715359587:ℚ)/22880000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((56271229:ℚ)/125000000),((2062747985337594458831518526570322105975173085263343999651497:ℚ)/37969840682716800000000000000000000000000000000000000000000000),((-529139620432771314217428029:ℚ)/1478656000000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((1392464121:ℚ)/2000000000),((7146778633:ℚ)/10000000000),((2032464121:ℚ)/5910000000),((9834778633:ℚ)/23260000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4125663909:ℚ)/10000000000),((20629278500435470762440313218539044517976180618356335277889:ℚ)/381550137020768750000000000000000000000000000000000000000000),((-533474810460740420996446949:ℚ)/1478656000000000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((885222617:ℚ)/1250000000),((7266176337:ℚ)/10000000000),((1285222617:ℚ)/3753125000),((3318058779:ℚ)/7880000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((3714189831:ℚ)/10000000000),((118776760473760564723518528868609595785037765927301184431243:ℚ)/2205538732114600000000000000000000000000000000000000000000000),((-1613344303809238747167605087:ℚ)/4435968000000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((1800304649:ℚ)/2500000000),((7385553707:ℚ)/10000000000),((2600304649:ℚ)/7625000000),((10073553707:ℚ)/24020000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3253817459:ℚ)/10000000000),((141822568380949690786614833279144345169267118440588795231:ℚ)/2641793491525000000000000000000000000000000000000000000000),((-28529450022654914632819711:ℚ)/77824000000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((228769833:ℚ)/312500000),((1524850233:ℚ)/2000000000),((328769833:ℚ)/982812500),((2062450233:ℚ)/4880000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((2719780541:ℚ)/10000000000),((1997885322213675583144381069725016115624169976054538734929:ℚ)/35921195928400000000000000000000000000000000000000000000000),((-11203033153752651:ℚ)/30400000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((1511881187:ℚ)/2000000000),((7862877901:ℚ)/10000000000),((717293729:ℚ)/2160000000),((10550877901:ℚ)/25160000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((258507401:ℚ)/2500000000),((2009985110185669293689600711115997449053281444186403776357:ℚ)/36283523956200000000000000000000000000000000000000000000000),((-73271174126740289:ℚ)/194560000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((77981021:ℚ)/100000000),((9769954867:ℚ)/10000000000),((109981021:ℚ)/400000000),((12457954867:ℚ)/25920000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((775959465429944541989207541415487976091923773968374457:ℚ)/10203667200000000000000000000000000000000000000000000000),((-193522087:ℚ)/512000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((2426403619:ℚ)/2500000000),((6789121861:ℚ)/5000000000),((1075467873:ℚ)/4600000000),((8133121861:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1106585696325519662876681:ℚ)/10580000000000000000000000),((-193522087:ℚ)/512000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC21
#check @N11Formalization.C450Source22GroupedC21.bound
#print axioms N11Formalization.C450Source22GroupedC21.valid0
#print axioms N11Formalization.C450Source22GroupedC21.valid1
#print axioms N11Formalization.C450Source22GroupedC21.valid2
#print axioms N11Formalization.C450Source22GroupedC21.valid3
#print axioms N11Formalization.C450Source22GroupedC21.valid4
#print axioms N11Formalization.C450Source22GroupedC21.valid5
#print axioms N11Formalization.C450Source22GroupedC21.valid6
#print axioms N11Formalization.C450Source22GroupedC21.valid7
#print axioms N11Formalization.C450Source22GroupedC21.valid8
#print axioms N11Formalization.C450Source22GroupedC21.valid9
#print axioms N11Formalization.C450Source22GroupedC21.valid10
#print axioms N11Formalization.C450Source22GroupedC21.bound
#print axioms N11Formalization.C450Source22GroupedC21.endpoint_checks
