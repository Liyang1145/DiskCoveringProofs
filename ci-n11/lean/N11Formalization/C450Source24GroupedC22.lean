import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((2898030287:ℚ)/5000000000),((1269490091:ℚ)/2000000000),((1435343429:ℚ)/3560000000),((5280470273:ℚ)/9920000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7034121851:ℚ)/10000000000),((109407313608430287508113:ℚ)/3168400000000000000000000),((-1093662197420056788400289:ℚ)/2957312000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((6275290777:ℚ)/10000000000),((1317353909:ℚ)/2000000000),((9091290777:ℚ)/22120000000),((5424061727:ℚ)/10680000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5993611741:ℚ)/10000000000),((1101597591123380315079170727548843:ℚ)/46452000000000000000000000000000000),((-1134016284243627666568289:ℚ)/2957312000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/16),((3:ℚ)/8),((6514685213:ℚ)/10000000000),((6706382499:ℚ)/10000000000),((9330685213:ℚ)/22500000000),((27479147497:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((67624683:ℚ)/125000000),((16682648083275916287900191316064889266609567412892158147:ℚ)/873603478125000000000000000000000000000000000000000000000),((-28850735585115801814881969:ℚ)/73932800000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((6634333889:ℚ)/10000000000),((3412983243:ℚ)/5000000000),((9450333889:ℚ)/22880000000),((13918949729:ℚ)/28125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5096021303:ℚ)/10000000000),((26949139260885407473205880363171098094315128129196804995411:ℚ)/1421672916412353515625000000000000000000000000000000000000000),((-382005493729260471485499:ℚ)/972800000000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((1350790477:ℚ)/2000000000),((1389104589:ℚ)/2000000000),((1913990477:ℚ)/4652000000),((5639313767:ℚ)/11440000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2381712481:ℚ)/5000000000),((89534804561594590420901607848743161152263182237291386483719:ℚ)/4746230085339600000000000000000000000000000000000000000000000),((-1168467070065105517330449:ℚ)/2957312000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((3436771101:ℚ)/5000000000),((7065053221:ℚ)/10000000000),((4844771101:ℚ)/11820000000),((28555159663:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((220396689:ℚ)/500000000),((336590345816415135912946908869958702352516395026178975546799:ℚ)/17885162672848535156250000000000000000000000000000000000000000),((-29388517296158408823476929:ℚ)/73932800000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((6993104743:ℚ)/10000000000),((7184558573:ℚ)/10000000000),((9809104743:ℚ)/24020000000),((28913675719:ℚ)/59100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4023447843:ℚ)/10000000000),((52531645346140768512599208081588192715755192180180213779599463:ℚ)/2791384957832540625000000000000000000000000000000000000000000000),((-29562942920045802851006801:ℚ)/73932800000000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((3556320659:ℚ)/5000000000),((7304040179:ℚ)/10000000000),((4964320659:ℚ)/12200000000),((29272120537:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3600651883:ℚ)/10000000000),((47492374744416698606630236824923384620388034968078351910907:ℚ)/2517959421609765625000000000000000000000000000000000000000000),((-29734957138649576991683729:ℚ)/73932800000000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((7232153157:ℚ)/10000000000),((7542936511:ℚ)/10000000000),((10048153157:ℚ)/25160000000),((29988809533:ℚ)/61000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1561993291:ℚ)/5000000000),((1574665872472164901663354265977227428247284119903261481296023:ℚ)/70158585797656250000000000000000000000000000000000000000000000),((-29756141049675072460510249:ℚ)/73932800000000000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((1494221433:ℚ)/2000000000),((3890875139:ℚ)/5000000000),((2057421433:ℚ)/5184000000),((15352625417:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1844328577:ℚ)/10000000000),((14409440532132487831842367867481019731462345448967739934803:ℚ)/637796319542578125000000000000000000000000000000000000000000),((-19944460779329897:ℚ)/48640000000000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((60234181:ℚ)/78125000),((4845000001:ℚ)/5000000000),((82234181:ℚ)/250000000),((18215000003:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((6829084689439730128720656632249:ℚ)/117187500000000000000000000000000),((-53074871:ℚ)/128000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((1202320609:ℚ)/1250000000),((33749147:ℚ)/25000000),((1554320609:ℚ)/5520000000),((119647441:ℚ)/200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((764823045421058605194233:ℚ)/7617600000000000000000000),((-53074871:ℚ)/128000000)⟩
theorem valid11 : Valid source24 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source24 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source24 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC22
#check @N11Formalization.C450Source24GroupedC22.bound
#print axioms N11Formalization.C450Source24GroupedC22.valid0
#print axioms N11Formalization.C450Source24GroupedC22.valid1
#print axioms N11Formalization.C450Source24GroupedC22.valid2
#print axioms N11Formalization.C450Source24GroupedC22.valid3
#print axioms N11Formalization.C450Source24GroupedC22.valid4
#print axioms N11Formalization.C450Source24GroupedC22.valid5
#print axioms N11Formalization.C450Source24GroupedC22.valid6
#print axioms N11Formalization.C450Source24GroupedC22.valid7
#print axioms N11Formalization.C450Source24GroupedC22.valid8
#print axioms N11Formalization.C450Source24GroupedC22.valid9
#print axioms N11Formalization.C450Source24GroupedC22.valid10
#print axioms N11Formalization.C450Source24GroupedC22.valid11
#print axioms N11Formalization.C450Source24GroupedC22.bound
#print axioms N11Formalization.C450Source24GroupedC22.endpoint_checks
