import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((5496616953:ℚ)/10000000000),((757637069:ℚ)/1250000000),((65469552577:ℚ)/106800000000),((965637069:ℚ)/1240000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7623152087:ℚ)/10000000000),((-14837151695537071295741972852770775351:ℚ)/101515536000000000000000000000000000000),((-97761011111734647518548353:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((2987722633:ℚ)/5000000000),((252015027:ℚ)/400000000),((34889503697:ℚ)/55300000000),((318575027:ℚ)/427200000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((266436599:ℚ)/400000000),((-175674629057733107104922084191204862822451900816586737159:ℚ)/1056952356250000000000000000000000000000000000000000000000),((-10043116836839833967372417:ℚ)/23658496000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((9:ℚ)/16),((5:ℚ)/8),((6214659949:ℚ)/10000000000),((6419969681:ℚ)/10000000000),((71931939541:ℚ)/112500000000),((8083969681:ℚ)/11060000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3066801267:ℚ)/5000000000),((-173333427359128396101301280784187054355969205415405302763:ℚ)/988769531250000000000000000000000000000000000000000000000),((-6286137825590526741469511353:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((3167111701:ℚ)/5000000000),((3269767681:ℚ)/5000000000),((36504005309:ℚ)/57200000000),((4101767681:ℚ)/5625000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5854736421:ℚ)/10000000000),((-18615811201757345493036799443545790298035593055448304113:ℚ)/106334800000000000000000000000000000000000000000000000000),((-1568503185567805941794259353:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((3226879783:ℚ)/5000000000),((53272593:ℚ)/80000000),((37041918047:ℚ)/58150000000),((66584593:ℚ)/91520000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5563678043:ℚ)/10000000000),((-53707586075955895317573045787839450581285585563474446969:ℚ)/307233934960937500000000000000000000000000000000000000000),((-400722227570075092699577:ℚ)/946339840000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((1314653959:ℚ)/2000000000),((3389293643:ℚ)/5000000000),((15031885631:ℚ)/23640000000),((4221293643:ℚ)/5815000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1314593511:ℚ)/2500000000),((-1200908764956960093591906708237108575754099486374735779:ℚ)/6880835700000000000000000000000000000000000000000000000),((-1561988570400051273466080977:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((1673188839:ℚ)/2500000000),((3449038037:ℚ)/5000000000),((19058699551:ℚ)/30025000000),((1427012679:ℚ)/1970000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((987230337:ℚ)/2000000000),((-29474367196974240408610173680549106001329481492589025873:ℚ)/169172226660156250000000000000000000000000000000000000000),((-1558505354705727791330437137:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((3406108717:ℚ)/5000000000),((3508770821:ℚ)/5000000000),((38654978453:ℚ)/61000000000),((4340770821:ℚ)/6005000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4593420503:ℚ)/10000000000),((-246704684148934231643001333978537811333717005010499442451:ℚ)/1418631250000000000000000000000000000000000000000000000000),((-1554871612495490613312631793:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((3465828569:ℚ)/5000000000),((58051259:ℚ)/80000000),((39192457121:ℚ)/62900000000),((71363259:ℚ)/97600000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((169006377:ℚ)/400000000),((-64416549521434817288799954017235354133396380730998012503:ℚ)/388840920312500000000000000000000000000000000000000000000),((-394747817319499068953713:ℚ)/946339840000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((7170473529:ℚ)/10000000000),((468449523:ℚ)/625000000),((80534261761:ℚ)/129600000000),((572449523:ℚ)/786250000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((67561627:ℚ)/200000000),((-27751555673522738866665090299425213213793342914069017407:ℚ)/167961600000000000000000000000000000000000000000000000000),((-23963516244246293484338817:ℚ)/57760000000000000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((3704606059:ℚ)/5000000000),((4701630851:ℚ)/5000000000),((41341454531:ℚ)/80000000000),((1844543617:ℚ)/2160000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((449082709:ℚ)/2000000000),((-17645614544868205609563378475711555446915736615755277557:ℚ)/200000000000000000000000000000000000000000000000000000000),((-2525690448235333:ℚ)/6080000000000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((2329247629:ℚ)/2500000000),((13212709847:ℚ)/10000000000),((24963228661:ℚ)/55200000000),((14876709847:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-44276078236797615532688429:ℚ)/1523520000000000000000000000),((-427667083:ℚ)/1024000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source27 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source27 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC26
#check @N11Formalization.C450Source27GroupedC26.bound
#print axioms N11Formalization.C450Source27GroupedC26.valid0
#print axioms N11Formalization.C450Source27GroupedC26.valid1
#print axioms N11Formalization.C450Source27GroupedC26.valid2
#print axioms N11Formalization.C450Source27GroupedC26.valid3
#print axioms N11Formalization.C450Source27GroupedC26.valid4
#print axioms N11Formalization.C450Source27GroupedC26.valid5
#print axioms N11Formalization.C450Source27GroupedC26.valid6
#print axioms N11Formalization.C450Source27GroupedC26.valid7
#print axioms N11Formalization.C450Source27GroupedC26.valid8
#print axioms N11Formalization.C450Source27GroupedC26.valid9
#print axioms N11Formalization.C450Source27GroupedC26.valid10
#print axioms N11Formalization.C450Source27GroupedC26.valid11
#print axioms N11Formalization.C450Source27GroupedC26.bound
#print axioms N11Formalization.C450Source27GroupedC26.endpoint_checks
