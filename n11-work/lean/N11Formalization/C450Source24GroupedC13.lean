import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((6304448263:ℚ)/10000000000),((1321114211:ℚ)/2000000000),((-617114211:ℚ)/4960000000),((-4193344789:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2962629961:ℚ)/5000000000),((62266864067921623424078757060592635616094285163019934314093:ℚ)/317573784375000000000000000000000000000000000000000000000000),((-81306258492128719299062583:ℚ)/591462400000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((409012689:ℚ)/625000000),((6845294781:ℚ)/10000000000),((-3325294781:ℚ)/25750000000),((-307038067:ℚ)/6675000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((2667038629:ℚ)/5000000000),((4658127678281887199541768377408485707160439102102511361:ℚ)/23932114123535156250000000000000000000000000000000000000),((-346383853521777989976647:ℚ)/2310400000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((1356759041:ℚ)/2000000000),((6965097557:ℚ)/10000000000),((-3445097557:ℚ)/26700000000),((-1126277123:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((467706511:ℚ)/1000000000),((1644109644592352005062727699945386797550910341503848611461:ℚ)/8573139732525000000000000000000000000000000000000000000000),((-3843280947718370703995367:ℚ)/23658496000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((1725883937:ℚ)/2500000000),((442803981:ℚ)/625000000),((-222803981:ℚ)/1698437500),((-1497651811:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4314508727:ℚ)/10000000000),((91983380963881733389270465814534541491294267125698685453:ℚ)/480848442205810546875000000000000000000000000000000000000),((-6237559272631179006262183:ℚ)/36966400000000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((3511620923:ℚ)/5000000000),((1440919017:ℚ)/2000000000),((-736919017:ℚ)/5530000000),((-3174862769:ℚ)/56250000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3920943899:ℚ)/10000000000),((687936099070941475960357782648659909751516700926061758839:ℚ)/3604325652122497558593750000000000000000000000000000000000),((-25882492656049326495141903:ℚ)/147865600000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((7142915271:ℚ)/10000000000),((1831073371:ℚ)/2500000000),((-105674819:ℚ)/781250000),((-609885983:ℚ)/10400000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((435730153:ℚ)/1250000000),((669580467811720349612369303522751416007351155234783163:ℚ)/3515200000000000000000000000000000000000000000000000000),((-297144421852681176353567:ℚ)/1638400000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((1815639419:ℚ)/2500000000),((1488792107:ℚ)/2000000000),((-71344737:ℚ)/520000000),((-1766918257:ℚ)/29075000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1495540321:ℚ)/5000000000),((14604608528234126184606681654018136791518598710115680853:ℚ)/76808483740234375000000000000000000000000000000000000000),((-6938655505894347420368527:ℚ)/36966400000000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((1845542651:ℚ)/2500000000),((1890899443:ℚ)/2500000000),((-1010899443:ℚ)/7268750000),((-1856627953:ℚ)/29550000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2399988959:ℚ)/10000000000),((164846804602684295607543485900209274953843899979675449197:ℚ)/868317265527343750000000000000000000000000000000000000000),((-7173629120950721212024207:ℚ)/36966400000000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((937719437:ℚ)/1250000000),((7802788459:ℚ)/10000000000),((-1427596153:ℚ)/9850000000),((-973158311:ℚ)/15250000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((201206173:ℚ)/1250000000),((1251882477562425115194564999355102488958540075640227729189:ℚ)/6550086474609375000000000000000000000000000000000000000000),((-1852311047862221024301183:ℚ)/9241600000000000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((1548169297:ℚ)/2000000000),((8280869521:ℚ)/10000000000),((-4760869521:ℚ)/30500000000),((-1700507891:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((214230334843447529358969954491738300423272011409000207313:ℚ)/1106531020800000000000000000000000000000000000000000000000),((-210618669:ℚ)/1024000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((410937301:ℚ)/500000000),((10190245983:ℚ)/10000000000),((-6670245983:ℚ)/32400000000),((-496811903:ℚ)/8000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((27053449219008259136801003890232035880212195796488953643:ℚ)/129600000000000000000000000000000000000000000000000000000),((-210618669:ℚ)/1024000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((5063785601:ℚ)/5000000000),((1750152499:ℚ)/1250000000),((-1310152499:ℚ)/5000000000),((-7831356803:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((743865290430901367746147048971272577620587888308949818029:ℚ)/3153686400000000000000000000000000000000000000000000000000),((-210618669:ℚ)/1024000000)⟩
theorem valid11 : Valid source24 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC13
#check @N11Formalization.C450Source24GroupedC13.bound
#print axioms N11Formalization.C450Source24GroupedC13.valid0
#print axioms N11Formalization.C450Source24GroupedC13.valid1
#print axioms N11Formalization.C450Source24GroupedC13.valid2
#print axioms N11Formalization.C450Source24GroupedC13.valid3
#print axioms N11Formalization.C450Source24GroupedC13.valid4
#print axioms N11Formalization.C450Source24GroupedC13.valid5
#print axioms N11Formalization.C450Source24GroupedC13.valid6
#print axioms N11Formalization.C450Source24GroupedC13.valid7
#print axioms N11Formalization.C450Source24GroupedC13.valid8
#print axioms N11Formalization.C450Source24GroupedC13.valid9
#print axioms N11Formalization.C450Source24GroupedC13.valid10
#print axioms N11Formalization.C450Source24GroupedC13.valid11
#print axioms N11Formalization.C450Source24GroupedC13.bound
#print axioms N11Formalization.C450Source24GroupedC13.endpoint_checks
