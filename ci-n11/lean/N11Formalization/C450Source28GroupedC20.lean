import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/16),((1:ℚ)/4),((146029457:ℚ)/250000000),((6160928829:ℚ)/10000000000),((854088371:ℚ)/2575000000),((10480928829:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1735459653:ℚ)/2500000000),((36994580804178262594316267075340578243:ℚ)/40454748032000000000000000000000000000000),((-86813061237295954034987861:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((243280007:ℚ)/400000000),((6401366427:ℚ)/10000000000),((1395440021:ℚ)/4272000000),((10721366427:ℚ)/25750000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((3215311729:ℚ)/5000000000),((2558564906977309047281434459508001341554605324001613863:ℚ)/3301807619857788085937500000000000000000000000000000000000),((-88515519529891538729707109:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((1264516211:ℚ)/2000000000),((6521506837:ℚ)/10000000000),((7121548633:ℚ)/21740000000),((10841506837:ℚ)/26700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1470600123:ℚ)/2500000000),((-1167075333308246696546632629383414094732553289792124616978261:ℚ)/421690817657756250000000000000000000000000000000000000000000000),((-90655995990367746873022149:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((3221394607:ℚ)/5000000000),((6641598663:ℚ)/10000000000),((17984183821:ℚ)/55300000000),((10961598663:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((279547561:ℚ)/500000000),((-6190055074587954331076472895043282205135406324618341937357:ℚ)/2397281067547161865234375000000000000000000000000000000000000),((-91483848240126608282925149:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((6562946379:ℚ)/10000000000),((6761644421:ℚ)/10000000000),((36328839137:ℚ)/112500000000),((11081644421:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2642686647:ℚ)/5000000000),((-1203150812799389083380704490856958533801664140016013859:ℚ)/509602028906250000000000000000000000000000000000000000000),((-92302676624602406791581861:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((3341527597:ℚ)/5000000000),((3440823227:ℚ)/5000000000),((18344582791:ℚ)/57200000000),((5600823227:ℚ)/14062500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2481511107:ℚ)/5000000000),((-748523855967475933213030685388173710562225950757109742753:ℚ)/355418229103088378906250000000000000000000000000000000000000),((-23278127517520258519158309:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((3401559061:ℚ)/5000000000),((140032139:ℚ)/200000000),((18524677183:ℚ)/58150000000),((226432139:ℚ)/572000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((924070391:ℚ)/2000000000),((-2158467202483002521275484339098889676526168212764973923:ℚ)/1186557521334900000000000000000000000000000000000000000000),((-37565350205845088177541:ℚ)/92416000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((6923137461:ℚ)/10000000000),((7121527953:ℚ)/10000000000),((37409412383:ℚ)/118200000000),((11441527953:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((531551849:ℚ)/1250000000),((-6714957148677420520822503179522452034507058831260443204081:ℚ)/4471290668212133789062500000000000000000000000000000000000000),((-94705298090725739831032589:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((1760778839:ℚ)/2500000000),((3680629499:ℚ)/5000000000),((9442336517:ℚ)/30500000000),((5840629499:ℚ)/14775000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((60186501:ℚ)/156250000),((435730504689298776709739690360904397854424252569037466773:ℚ)/225031549567675781250000000000000000000000000000000000000000),((-23740739847114697590310821:ℚ)/57760000000000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((7282954717:ℚ)/10000000000),((392016179:ℚ)/500000000),((38488864151:ℚ)/129600000000),((608016179:ℚ)/1525000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((2898613439:ℚ)/10000000000),((99216925677047067490893329869107298225826942150888197:ℚ)/12119322436523437500000000000000000000000000000000000000),((-3173988439546347:ℚ)/7600000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((7762216379:ℚ)/10000000000),((4876342203:ℚ)/5000000000),((39926649137:ℚ)/160000000000),((2345447401:ℚ)/5400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((6386244492142295200876982591141023827675666424839863:ℚ)/184528125000000000000000000000000000000000000000000000),((-6919959:ℚ)/16000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((9675174707:ℚ)/10000000000),((13567137373:ℚ)/10000000000),((45665524121:ℚ)/220800000000),((17887137373:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((627723095562753040601181308474778866499:ℚ)/8464000000000000000000000000000000000000),((-6919959:ℚ)/16000000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC20
#check @N11Formalization.C450Source28GroupedC20.bound
#print axioms N11Formalization.C450Source28GroupedC20.valid0
#print axioms N11Formalization.C450Source28GroupedC20.valid1
#print axioms N11Formalization.C450Source28GroupedC20.valid2
#print axioms N11Formalization.C450Source28GroupedC20.valid3
#print axioms N11Formalization.C450Source28GroupedC20.valid4
#print axioms N11Formalization.C450Source28GroupedC20.valid5
#print axioms N11Formalization.C450Source28GroupedC20.valid6
#print axioms N11Formalization.C450Source28GroupedC20.valid7
#print axioms N11Formalization.C450Source28GroupedC20.valid8
#print axioms N11Formalization.C450Source28GroupedC20.valid9
#print axioms N11Formalization.C450Source28GroupedC20.valid10
#print axioms N11Formalization.C450Source28GroupedC20.valid11
#print axioms N11Formalization.C450Source28GroupedC20.bound
#print axioms N11Formalization.C450Source28GroupedC20.endpoint_checks
