import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),(0:ℚ),((1:ℚ)/16),((6047497441:ℚ)/10000000000),((6359355807:ℚ)/10000000000),((16:ℚ)/103),((22999355807:ℚ)/99200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1301190741:ℚ)/2000000000),((297451017399264755774441337314950108538933:ℚ)/2589103874048000000000000000000000000000000),((-13931809692266839645565134979:ℚ)/44359680000000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((6288269333:ℚ)/10000000000),((1319933711:ℚ)/2000000000),((40:ℚ)/267),((4647933711:ℚ)/20600000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5963272053:ℚ)/10000000000),((1722242242848792401676397882949151736651048740302883076847:ℚ)/15214729512304687500000000000000000000000000000000000000000),((-192816278695771757076436897:ℚ)/591462400000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((6528803907:ℚ)/10000000000),((839968741:ℚ)/1250000000),((160:ℚ)/1087),((2919968741:ℚ)/13350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5373792709:ℚ)/10000000000),((647212915162333440619433527790814376967115254176994268554711:ℚ)/5856816911913281250000000000000000000000000000000000000000000),((-78169165288290736703041817:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((1662247543:ℚ)/2500000000),((6839784813:ℚ)/10000000000),((80:ℚ)/553),((23479784813:ℚ)/108700000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((5056349019:ℚ)/10000000000),((2411492401016486110774445020394111941971440679105119393617587:ℚ)/21917998331859765625000000000000000000000000000000000000000000),((-15271858140058483960874783099:ℚ)/44359680000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((3384563111:ℚ)/5000000000),((3479887807:ℚ)/5000000000),((32:ℚ)/225),((11799887807:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((235984857:ℚ)/500000000),((1340625100162683157116655403779040226374281712007602261737:ℚ)/12230448693750000000000000000000000000000000000000000000000),((-1294564628076048430663580993:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((6889214659:ℚ)/10000000000),((7079724573:ℚ)/10000000000),((20:ℚ)/143),((23719724573:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4359350339:ℚ)/10000000000),((2209410613183701747923434672355326530234504923091676936277821:ℚ)/20219348144531250000000000000000000000000000000000000000000000),((-15797238056073301758502917659:ℚ)/44359680000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((7009257909:ℚ)/10000000000),((3599816891:ℚ)/5000000000),((160:ℚ)/1163),((11919816891:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1984409273:ℚ)/5000000000),((43109237437891401085349028966129100592000063334321794912814003:ℚ)/395519173778300000000000000000000000000000000000000000000000000),((-1338270951084903956573507417:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((7129258233:ℚ)/10000000000),((3659752597:ℚ)/5000000000),((80:ℚ)/591),((11979752597:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((176903793:ℚ)/500000000),((1296978497212560349600853714457083671537109824209528806441901:ℚ)/11923441781899023437500000000000000000000000000000000000000000),((-1360068411226044778112757113:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((453076109:ℚ)/625000000),((7559141819:ℚ)/10000000000),((8:ℚ)/61),((24199141819:ℚ)/118200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((381260459:ℚ)/1250000000),((1404736445338880974250163490787586339975061370251642096759801:ℚ)/12801794819850000000000000000000000000000000000000000000000000),((-5520039278116489166038367577:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((1497804421:ℚ)/2000000000),((2009508647:ℚ)/2500000000),((10:ℚ)/81),((6169508647:ℚ)/30500000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((342204989:ℚ)/2000000000),((32430795258687346170041418738277956853456942196254752348431:ℚ)/290863738476562500000000000000000000000000000000000000000000),((-3753851969900247:ℚ)/9728000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((7968220087:ℚ)/10000000000),((4974937187:ℚ)/5000000000),((1:ℚ)/10),((164135027:ℚ)/800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((24088516237463075586631354635971722669543219170459:ℚ)/200000000000000000000000000000000000000000000000000),((-401177891:ℚ)/1024000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((1235123171:ℚ)/1250000000),((1376372043:ℚ)/1000000000),((5:ℚ)/69),((3040372043:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((711852117935670502871202987978645316793:ℚ)/4875264000000000000000000000000000000000),((-401177891:ℚ)/1024000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC17
#check @N11Formalization.C450Source27GroupedC17.bound
#print axioms N11Formalization.C450Source27GroupedC17.valid0
#print axioms N11Formalization.C450Source27GroupedC17.valid1
#print axioms N11Formalization.C450Source27GroupedC17.valid2
#print axioms N11Formalization.C450Source27GroupedC17.valid3
#print axioms N11Formalization.C450Source27GroupedC17.valid4
#print axioms N11Formalization.C450Source27GroupedC17.valid5
#print axioms N11Formalization.C450Source27GroupedC17.valid6
#print axioms N11Formalization.C450Source27GroupedC17.valid7
#print axioms N11Formalization.C450Source27GroupedC17.valid8
#print axioms N11Formalization.C450Source27GroupedC17.valid9
#print axioms N11Formalization.C450Source27GroupedC17.valid10
#print axioms N11Formalization.C450Source27GroupedC17.valid11
#print axioms N11Formalization.C450Source27GroupedC17.bound
#print axioms N11Formalization.C450Source27GroupedC17.endpoint_checks
